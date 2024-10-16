use crate::constants::{ETH_DECIMALS, USDT_DECIMALS, VOB_DEPTH};
use crate::events::uniswap::Side;
use crate::orderbook::logic::{calculate_reserve_adjustment, calculate_reserves};
use crate::utils::logic::decimal_to_u256;
use num_traits::{One, Zero};
use rust_decimal::Decimal;
use std::collections::BTreeMap;
use std::fmt::Display;
use tracing::{debug, info, warn};
use web3::types::U256;

/// `SwapInfo` is a structure that holds information about a cryptocurrency swap transaction.
///
/// # Fields
/// - `eth_in` (`U256`): The amount of Ethereum (ETH) that is being swapped into the transaction.
/// - `usdt_in` (`U256`): The amount of Tether (USDT) that is being swapped into the transaction.
/// - `eth_out` (`U256`): The amount of Ethereum (ETH) that is received from the transaction.
/// - `usdt_out` (`U256`): The amount of Tether (USDT) that is received from the transaction.
/// - `effective_price` (`Decimal`): The effective price of the transaction, expressed as a decimal value.
/// - `side` (`Side`): Indicates the side of the transaction (e.g., buying or selling).
#[derive(Debug, Clone)]
pub(crate) struct SwapInfo {
    pub(crate) eth_in: U256,
    pub(crate) usdt_in: U256,
    pub(crate) eth_out: U256,
    pub(crate) usdt_out: U256,
    pub(crate) effective_price: Decimal,
    pub(crate) side: Side,
}

/// `VirtualOrderBook` represents a virtual order book for tracking bids, asks, and reserves for cryptocurrencies.
///
/// # Fields
/// - `bids`: A `BTreeMap` storing bid prices and their corresponding amounts.
/// - `asks`: A `BTreeMap` storing ask prices and their corresponding amounts.
/// - `reserve_eth`: A `U256` value tracking ETH reserves in the order book.
/// - `reserve_usdt`: A `U256` value tracking USDT reserves in the order book.
/// - `last_swap`: An optional `SwapInfo` that keeps the last swap event information.
/// - `side`: A `Side` indicating whether this book is for buying or selling ETH.
#[derive(Debug, Clone)]
pub(crate) struct VirtualOrderBook {
    bids: BTreeMap<Decimal, Decimal>, // Stores bids in the order book
    asks: BTreeMap<Decimal, Decimal>, // Stores asks in the order book
    reserve_eth: U256,                // Tracks ETH reserves in the order book
    reserve_usdt: U256,               // Tracks USDT reserves in the order book
    last_swap: Option<SwapInfo>,      // Keeps the last swap event
    side: Side,                       // Indicates if this book is for buying or selling ETH
}

impl Display for VirtualOrderBook {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut result = String::new();
        match self.last_swap.as_ref() {
            Some(swap) => {
                result.push_str(&format!("\n\tEffective Price: {}\n", swap.effective_price));
            }
            None => {
                result.push_str("\n\tEffective Price: N/A\n");
            }
        }

        result.push_str("\tAsks:\n");
        for (price, amount) in self.asks.iter().rev() {
            result.push_str(&format!("\t\tPrice: {}, Amount: {}\n", price, amount));
        }

        result.push_str("\tBids:\n");
        for (price, amount) in self.bids.iter().rev() {
            result.push_str(&format!("\t\tPrice: {}, Amount: {}\n", price, amount));
        }

        write!(f, "{}", result)
    }
}

impl VirtualOrderBook {
    /// Updates the reserves based on a new swap event. It initializes the reserves using the first two swap events
    /// and continues to update them after initialization.
    ///
    /// # Arguments
    /// * `swap`: A `SwapInfo` instance containing information about the swap event.
    pub fn update_reserves(&mut self, swap: SwapInfo) {
        // If the side of the swap doesn't match the book's side, log a warning
        if swap.side != self.side {
            warn!(
                "Side mismatch. Expected: {:?}, got: {:?}",
                self.side, swap.side
            );
            return;
        }

        // If there is no previous swap, store the current one and return
        if self.last_swap.is_none() {
            self.last_swap = Some(swap);
            return;
        }

        // Initialize the reserves if not already done
        if self.reserve_eth == U256::zero() || self.reserve_usdt == U256::zero() {
            let last_swap = self.last_swap.clone().unwrap();

            let (reserve_eth, reserve_usdt) = calculate_reserves(&last_swap, &swap).unwrap();

            // Convert the calculated reserves back to U256
            self.reserve_eth = decimal_to_u256(reserve_eth, ETH_DECIMALS);
            self.reserve_usdt = decimal_to_u256(reserve_usdt, USDT_DECIMALS);

            // Store the current swap as the last swap
            self.last_swap = Some(swap);
        } else {
            info!("Updating reserves_eth: {} reserve_usdt:{} eth_in: {} usdt_in: {} eth_out: {} usdt_out: {}",
                self.reserve_eth, self.reserve_usdt, swap.eth_in, swap.usdt_in, swap.eth_out, swap.usdt_out
            );

            // After initialization, continue updating reserves normally
            self.reserve_eth += swap.eth_in.saturating_sub(swap.eth_out);
            self.reserve_usdt += swap.usdt_in.saturating_sub(swap.usdt_out);
        }
    }

    /// Updates the order book with new bids and asks based on the effective price.
    ///
    /// # Arguments
    /// * `effective_price`: The decimal effective price to update the order book.
    pub fn update_order_book(&mut self, effective_price: Decimal) {
        self.bids.clear();
        self.asks.clear();

        for i in 1..=VOB_DEPTH {
            let price_adjustment = Decimal::from(i as i64) / Decimal::from(1000);

            // Generate bid
            let bid_price = effective_price * (Decimal::one() - price_adjustment);
            self.calculate_and_add_order(bid_price, true);

            // Generate ask
            let ask_price = effective_price * (Decimal::one() + price_adjustment);
            self.calculate_and_add_order(ask_price, false);
        }
    }

    /// Calculates and adds an order to the bids or asks based on the price and whether it is a bid or not.
    ///
    /// # Arguments
    /// * `price`: The decimal price of the order.
    /// * `is_bid`: A boolean indicating if the order is a bid.
    fn calculate_and_add_order(&mut self, price: Decimal, is_bid: bool) {
        debug!("Calculating order: price = {}, is_bid = {}", price, is_bid);

        let (target_price_eth, target_price_usdt) = match (self.side, is_bid) {
            (Side::Buy, true) | (Side::Sell, false) => (Some(price), None),
            (Side::Buy, false) | (Side::Sell, true) => (None, Some(price)),
        };

        debug!(
            "Target prices: ETH = {:?}, USDT = {:?}",
            target_price_eth, target_price_usdt
        );

        match calculate_reserve_adjustment(
            self.reserve_eth,
            self.reserve_usdt,
            target_price_eth,
            target_price_usdt,
        ) {
            Ok((eth_adjustment, _)) => {
                let mut volume = eth_adjustment.abs();
                debug!("Calculated volume: {}", volume);

                // If the calculated volume is zero, use a small default volume
                if volume == Decimal::zero() {
                    volume = Decimal::new(1, 6); // 0.000001 ETH
                    debug!("Using default small volume: {}", volume);
                }

                match (self.side, is_bid) {
                    (Side::Buy, true) => {
                        debug!("Adding to bids: price = {}, volume = {}", price, volume);
                        self.bids.insert(price, volume);
                    }
                    (Side::Buy, false) => {
                        debug!("Adding to asks: price = {}, volume = {}", price, volume);
                        self.asks.insert(price, volume);
                    }
                    (Side::Sell, false) => {
                        debug!("Adding to asks: price = {}, volume = {}", price, volume);
                        self.asks.insert(price, volume);
                    }
                    (Side::Sell, true) => {
                        debug!("Adding to bids: price = {}, volume = {}", price, volume);
                        self.bids.insert(price, volume);
                    }
                };
            }
            Err(e) => {
                warn!("Failed to calculate reserve adjustment: {}", e);
            }
        }
    }
}

/// The `DualSideBook` structure maintains two virtual order books for ETH/USDT
/// and USDT/ETH swaps, allowing the storage and updating of the bid and ask
/// orders for each trading pair.
#[derive(Debug, Clone)]
pub(crate) struct DualSideBook {
    pub(crate) eth_usdt: VirtualOrderBook, // Order book for ETH/USDT swaps
    pub(crate) usdt_eth: VirtualOrderBook, // Order book for USDT/ETH swaps
}

impl DualSideBook {
    /// Initializes a new `DualSideBook` with empty order books for ETH/USDT
    /// and USDT/ETH trading pairs.
    pub(crate) fn new() -> Self {
        DualSideBook {
            eth_usdt: VirtualOrderBook {
                bids: BTreeMap::new(),
                asks: BTreeMap::new(),
                reserve_eth: U256::zero(),
                reserve_usdt: U256::zero(),
                last_swap: None,
                side: Side::Buy,
            },
            usdt_eth: VirtualOrderBook {
                bids: BTreeMap::new(),
                asks: BTreeMap::new(),
                reserve_eth: U256::zero(),
                reserve_usdt: U256::zero(),
                last_swap: None,
                side: Side::Sell,
            },
        }
    }

    /// Updates the relevant order book based on a swap transaction. The method
    /// updates reserves and adjusts the order book prices accordingly.
    ///
    /// # Arguments
    ///
    /// * `eth_in` - Amount of ETH received during the swap
    /// * `usdt_in` - Amount of USDT received during the swap
    /// * `eth_out` - Amount of ETH sent during the swap
    /// * `usdt_out` - Amount of USDT sent during the swap
    /// * `effective_price` - The effective price of the swap
    /// * `side` - The side of the order book to be updated (Buy or Sell)
    pub(crate) fn update_from_swap(
        &mut self,
        eth_in: U256,
        usdt_in: U256,
        eth_out: U256,
        usdt_out: U256,
        effective_price: Decimal,
        side: Side,
    ) {
        let swap = SwapInfo {
            eth_in,
            usdt_in,
            eth_out,
            usdt_out,
            effective_price,
            side,
        };

        match side {
            Side::Buy => {
                self.eth_usdt.update_reserves(swap);
                self.eth_usdt.update_order_book(effective_price);
            }
            Side::Sell => {
                self.usdt_eth.update_reserves(swap);
                self.usdt_eth.update_order_book(effective_price);
            }
        }
    }
}

impl Display for DualSideBook {
    /// Formats the `DualSideBook` into a readable string representation,
    /// showing the order books for both ETH/USDT and USDT/ETH trading pairs.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ETH/USDT Order Book:{}", self.eth_usdt)?;
        write!(f, "USDT/ETH Order Book:{}", self.usdt_eth)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests_update_reserves {
    use super::*;
    use crate::utils::logger::setup_logger;
    use crate::utils::logic::u256_to_decimals;
    use rust_decimal_macros::dec;
    use std::str::FromStr;

    fn create_swap_info(
        eth_in: u64,
        usdt_in: u64,
        eth_out: u64,
        usdt_out: u64,
        side: Side,
    ) -> SwapInfo {
        SwapInfo {
            eth_in: U256::from(eth_in),
            usdt_in: U256::from(usdt_in),
            eth_out: U256::from(eth_out),
            usdt_out: U256::from(usdt_out),
            effective_price: dec!(0), // Not relevant for these tests
            side,
        }
    }

    #[test]
    fn test_update_reserves_side_mismatch() {
        setup_logger();
        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let swap = create_swap_info(1, 0, 0, 2600, Side::Sell);
        vob.update_reserves(swap);

        assert_eq!(vob.reserve_eth, U256::zero());
        assert_eq!(vob.reserve_usdt, U256::zero());
        assert!(vob.last_swap.is_none());
    }

    #[test]
    fn test_update_reserves_first_swap() {
        setup_logger();
        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let swap = create_swap_info(0, 2600, 1, 0, Side::Buy);
        vob.update_reserves(swap.clone());

        assert_eq!(vob.reserve_eth, U256::zero());
        assert_eq!(vob.reserve_usdt, U256::zero());
        // assert_eq!(vob.last_swap, Some(swap));
    }

    #[test]
    fn test_update_reserves_initialize_buy() {
        setup_logger();
        let last_swap = Some(SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4800000000").unwrap(), // 4800 USDT with 6 decimals
            eth_out: U256::from_dec_str("1817457120942687720").unwrap(), // 1.817457120942687720 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        });

        // Second swap: 5000 USDT in, 1.892905982365873578 ETH out
        let swap = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("5000000000").unwrap(), // 5000 USDT with 6 decimals
            eth_out: U256::from_dec_str("1892905982365873578").unwrap(), // 1.892905982365873578 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        };

        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap,
            side: Side::Buy,
        };

        vob.update_reserves(swap.clone());
        let reserve_eth = u256_to_decimals(vob.reserve_eth, ETH_DECIMALS);
        let reserve_usdt = u256_to_decimals(vob.reserve_usdt, USDT_DECIMALS);
        info!("Reserves: ETH: {}, USDT: {}", reserve_eth, reserve_usdt);

        assert!(vob.reserve_eth > U256::zero());
        assert!(vob.reserve_usdt > U256::zero());
        assert_eq!(
            reserve_eth,
            Decimal::from_str("25220.583165107801329842").unwrap()
        );
        assert_eq!(reserve_usdt, Decimal::from_str("66604088.758666").unwrap());
    }

    #[test]
    fn test_update_reserves_initialize_sell() {
        setup_logger();

        // First swap: 0.127263917200000000 ETH in, 328.080223 USDT out
        let last_swap = Some(SwapInfo {
            eth_in: U256::from_dec_str("127263917200000000").unwrap(), // 0.1272639172 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("328080223").unwrap(), // 328.080223 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        });

        // Second swap: 0.194439766600168513 ETH in, 501.250000 USDT out
        let swap = SwapInfo {
            eth_in: U256::from_dec_str("194439766600168513").unwrap(), // 0.194439766600168513 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("501250000").unwrap(), // 501.250000 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        };

        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap,
            side: Side::Sell,
        };

        vob.update_reserves(swap.clone());
        let reserve_eth = u256_to_decimals(vob.reserve_eth, ETH_DECIMALS);
        let reserve_usdt = u256_to_decimals(vob.reserve_usdt, USDT_DECIMALS);
        info!("Reserves: ETH: {}, USDT: {}", reserve_eth, reserve_usdt);

        assert!(vob.reserve_eth > U256::zero());
        assert!(vob.reserve_usdt > U256::zero());
        assert_eq!(
            reserve_eth,
            Decimal::from_str("25540.851076387097252598").unwrap()
        );
        assert_eq!(reserve_usdt, Decimal::from_str("65843406.787145").unwrap());
    }

    #[test]
    fn test_update_reserves_normal_update() {
        setup_logger();

        let last_swap = Some(SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4800000000").unwrap(), // 4800 USDT with 6 decimals
            eth_out: U256::from_dec_str("1817457120942687720").unwrap(), // 1.817457120942687720 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        });

        // Second swap: 5000 USDT in, 1.892905982365873578 ETH out
        let swap = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("5000000000").unwrap(), // 5000 USDT with 6 decimals
            eth_out: U256::from_dec_str("1892905982365873578").unwrap(), // 1.892905982365873578 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        };

        let reserve_eth = Decimal::from_str("25540.8510763870972525985544").unwrap();
        let reserve_usdt = Decimal::from_str("65843406.787145506240089402637").unwrap();
        let reserve_eth_u256 = decimal_to_u256(reserve_eth, ETH_DECIMALS);
        let reserve_usdt_u256 = decimal_to_u256(reserve_usdt, USDT_DECIMALS);

        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: reserve_eth_u256,
            reserve_usdt: reserve_usdt_u256,
            last_swap,
            side: Side::Buy,
        };

        assert_eq!(reserve_eth, dec!(25540.8510763870972525985544));
        assert_eq!(reserve_usdt, dec!(65843406.787145506240089402637));

        vob.update_reserves(swap);

        assert_eq!(vob.reserve_eth, U256::from(25540851076387097252598_u128));
        assert_eq!(vob.reserve_usdt, U256::from(65848406787145_u128));

        let reserve_eth = u256_to_decimals(vob.reserve_eth, ETH_DECIMALS);
        let reserve_usdt = u256_to_decimals(vob.reserve_usdt, USDT_DECIMALS);

        assert_eq!(
            reserve_eth,
            Decimal::from_str("25540.851076387097252598").unwrap()
        );
        assert_eq!(reserve_usdt, Decimal::from_str("65848406.787145").unwrap());
    }

    #[test]
    fn test_update_reserves_sell_swap() {
        setup_logger();

        let last_swap = Some(SwapInfo {
            eth_in: U256::from_dec_str("127263917200000000").unwrap(), // 0.1272639172 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("328080223").unwrap(), // 328.080223 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        });

        let swap = SwapInfo {
            eth_in: U256::from_dec_str("194439766600168513").unwrap(), // 0.194439766600168513 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("501250000").unwrap(), // 501.250000 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        };

        let reserve_eth = Decimal::from_str("25540.8510763870972525985544").unwrap();
        let reserve_usdt = Decimal::from_str("65843406.787145506240089402637").unwrap();
        let reserve_eth_u256 = decimal_to_u256(reserve_eth, ETH_DECIMALS);
        let reserve_usdt_u256 = decimal_to_u256(reserve_usdt, USDT_DECIMALS);

        let mut vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: reserve_eth_u256,
            reserve_usdt: reserve_usdt_u256,
            last_swap,
            side: Side::Sell,
        };

        assert_eq!(reserve_eth, dec!(25540.8510763870972525985544));
        assert_eq!(reserve_usdt, dec!(65843406.787145506240089402637));

        vob.update_reserves(swap);

        assert_eq!(vob.reserve_eth, U256::from(25541045516153697421111_u128));
        assert_eq!(vob.reserve_usdt, U256::from(65843406787145_u128));

        let reserve_eth = u256_to_decimals(vob.reserve_eth, ETH_DECIMALS);
        let reserve_usdt = u256_to_decimals(vob.reserve_usdt, USDT_DECIMALS);

        assert_eq!(
            reserve_eth,
            Decimal::from_str("25541.045516153697421111").unwrap()
        );
        assert_eq!(reserve_usdt, Decimal::from_str("65843406.787145").unwrap());
    }
}

#[cfg(test)]
mod tests_calculate_and_add_order {
    use super::*;
    use crate::utils::logger::setup_logger;
    use rust_decimal_macros::dec;

    // Helper function to create a VirtualOrderBook with given reserves
    fn create_vob(reserve_eth: U256, reserve_usdt: U256, side: Side) -> VirtualOrderBook {
        VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth,
            reserve_usdt,
            last_swap: None,
            side,
        }
    }

    #[test]
    fn test_calculate_and_add_order_buy_side_bid() {
        std::env::set_var("LOGLEVEL", "debug");
        setup_logger();
        let mut vob = create_vob(
            U256::from(100_000_000_000_000_000_000u128), // 100 ETH
            U256::from(200_000_000_000u128),             // 200,000 USDT
            Side::Buy,
        );
        let price = dec!(2000); // 2000 USDT/ETH

        info!("Initial VOB state: {:?}", vob);

        vob.calculate_and_add_order(price, true);

        info!("Final VOB state: {:?}", vob);

        assert!(!vob.bids.is_empty(), "Bids should not be empty");
        assert_eq!(vob.bids.len(), 1, "Bids should contain exactly one order");
        assert!(
            vob.bids.contains_key(&price),
            "Bids should contain the price {}",
            price
        );

        if let Some(volume) = vob.bids.get(&price) {
            info!("Order added: price = {}, volume = {}", price, volume);
            assert!(
                *volume > Decimal::zero(),
                "Volume should be greater than zero"
            );
            assert!(
                *volume <= Decimal::one(),
                "Volume should be less than or equal to 1 ETH"
            );
        } else {
            panic!("No order found at price {}", price);
        }
    }

    #[test]
    fn test_calculate_and_add_order_buy_side_ask() {
        let mut vob = create_vob(
            U256::from(100_000_000_000_000_000_000u128), // 100 ETH
            U256::from(200_000_000_000u128),             // 200,000 USDT
            Side::Buy,
        );
        let price = dec!(2200); // 2200 USDT/ETH

        vob.calculate_and_add_order(price, false);

        assert!(!vob.asks.is_empty());
        assert_eq!(vob.asks.len(), 1);
        assert!(vob.asks.contains_key(&price));
    }

    #[test]
    fn test_calculate_and_add_order_sell_side_bid() {
        let mut vob = create_vob(
            U256::from(100_000_000_000_000_000_000u128), // 100 ETH
            U256::from(200_000_000_000u128),             // 200,000 USDT
            Side::Sell,
        );
        let price = dec!(1800); // 1800 USDT/ETH

        vob.calculate_and_add_order(price, true);

        assert!(!vob.bids.is_empty());
        assert_eq!(vob.bids.len(), 1);
        assert!(vob.bids.contains_key(&price));
    }

    #[test]
    fn test_calculate_and_add_order_sell_side_ask() {
        let mut vob = create_vob(
            U256::from(100_000_000_000_000_000_000u128), // 100 ETH
            U256::from(200_000_000_000u128),             // 200,000 USDT
            Side::Sell,
        );
        let price = dec!(2000); // 2000 USDT/ETH

        vob.calculate_and_add_order(price, false);

        assert!(!vob.asks.is_empty());
        assert_eq!(vob.asks.len(), 1);
        assert!(vob.asks.contains_key(&price));
    }

    #[test]
    fn test_update_order_book() {
        setup_logger();
        let mut vob = create_vob(
            U256::from(100_000_000_000_000_000_000u128), // 100 ETH
            U256::from(200_000_000_000u128),             // 200,000 USDT
            Side::Buy,
        );
        let effective_price = dec!(2000); // 2000 USDT/ETH

        vob.update_order_book(effective_price);

        assert!(!vob.bids.is_empty());
        assert!(!vob.asks.is_empty());
        assert_eq!(vob.bids.len(), VOB_DEPTH);
        assert_eq!(vob.asks.len(), VOB_DEPTH);
        info!("Order book: {}", vob);
    }
}

#[cfg(test)]
mod tests_virtual_orderbook_display {
    use super::*;
    use crate::utils::logger::setup_logger;
    use rust_decimal_macros::dec;

    #[test]
    fn test_display_empty_order_book() {
        setup_logger();
        let vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let display_output = format!("{}", vob);
        info!("{}", display_output);
        assert_eq!(
            display_output,
            "\n\tEffective Price: N/A\n\tAsks:\n\tBids:\n"
        );
    }

    #[test]
    fn test_display_order_book_with_bids_only() {
        setup_logger();
        let mut bids = BTreeMap::new();
        bids.insert(dec!(1900), dec!(0.5));
        bids.insert(dec!(1950), dec!(0.3));

        let vob = VirtualOrderBook {
            bids,
            asks: BTreeMap::new(),
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let display_output = format!("{}", vob);
        info!("{}", display_output);
        assert_eq!(
            display_output,
            "\n\tEffective Price: N/A\n\tAsks:\n\tBids:\n\t\tPrice: 1950, Amount: 0.3\n\t\tPrice: 1900, Amount: 0.5\n"
        );
    }

    #[test]
    fn test_display_order_book_with_asks_only() {
        setup_logger();
        let mut asks = BTreeMap::new();
        asks.insert(dec!(2050), dec!(0.4));
        asks.insert(dec!(2100), dec!(0.6));

        let vob = VirtualOrderBook {
            bids: BTreeMap::new(),
            asks,
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let display_output = format!("{}", vob);
        info!("{}", display_output);
        assert_eq!(
            display_output,
            "\n\tEffective Price: N/A\n\tAsks:\n\t\tPrice: 2100, Amount: 0.6\n\t\tPrice: 2050, Amount: 0.4\n\tBids:\n"
        );
    }

    #[test]
    fn test_display_order_book_with_bids_and_asks() {
        setup_logger();
        let mut bids = BTreeMap::new();
        bids.insert(dec!(1900), dec!(0.5));
        bids.insert(dec!(1950), dec!(0.3));

        let mut asks = BTreeMap::new();
        asks.insert(dec!(2050), dec!(0.4));
        asks.insert(dec!(2100), dec!(0.6));

        let vob = VirtualOrderBook {
            bids,
            asks,
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: None,
            side: Side::Buy,
        };

        let display_output = format!("{}", vob);
        info!("{}", display_output);
        assert_eq!(
            display_output,
            "\n\tEffective Price: N/A\n\tAsks:\n\t\tPrice: 2100, Amount: 0.6\n\t\tPrice: 2050, Amount: 0.4\n\tBids:\n\t\tPrice: 1950, Amount: 0.3\n\t\tPrice: 1900, Amount: 0.5\n"
        );
    }

    #[test]
    fn test_display_order_book_with_many_orders() {
        setup_logger();
        let mut bids = BTreeMap::new();
        let mut asks = BTreeMap::new();

        let swap = Some(SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4800000000").unwrap(),
            eth_out: U256::from_dec_str("1817457120942687720").unwrap(),
            usdt_out: U256::zero(),
            effective_price: dec!(1950.5224),
            side: Side::Buy,
        });

        for i in 0..5 {
            bids.insert(
                dec!(1900) - Decimal::from(i * 10),
                dec!(0.1) + Decimal::from(i) / dec!(10),
            );
            asks.insert(
                dec!(2000) + Decimal::from(i * 10),
                dec!(0.1) + Decimal::from(i) / dec!(10),
            );
        }

        let vob = VirtualOrderBook {
            bids,
            asks,
            reserve_eth: U256::zero(),
            reserve_usdt: U256::zero(),
            last_swap: swap,
            side: Side::Buy,
        };

        let display_output = format!("{}", vob);
        info!("{}", display_output);
        let expected_output = "\n\tEffective Price: 1950.5224\n\tAsks:\n\t\tPrice: 2040, Amount: 0.50\n\t\tPrice: 2030, Amount: 0.40\n\t\tPrice: 2020, Amount: 0.30\n\t\tPrice: 2010, Amount: 0.20\n\t\tPrice: 2000, Amount: 0.1\n\tBids:\n\t\tPrice: 1900, Amount: 0.1\n\t\tPrice: 1890, Amount: 0.20\n\t\tPrice: 1880, Amount: 0.30\n\t\tPrice: 1870, Amount: 0.40\n\t\tPrice: 1860, Amount: 0.50\n";
        assert_eq!(display_output, expected_output);
    }
}
