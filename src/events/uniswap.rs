use crate::constants::{ETH_DECIMALS, USDT_DECIMALS};
use crate::utils::logic::u256_to_decimals;
use ethabi::{Event, EventParam, ParamType, RawLog};
use num_traits::One;
use rust_decimal::Decimal;
use std::fmt::Display;
use tracing::{info, warn};
use web3::types::{Address, Log, H256, U256};

/// The `Side` enum represents the type of transaction in the trading context.
/// It can be either a `Buy` or a `Sell`.
///
/// # Examples
///
/// ```
/// use uniswapv2_vob::events::uniswap::Side;
///
/// let buy_side = Side::Buy;
/// let sell_side = Side::Sell;
///
/// assert_eq!(buy_side.to_string(), "Buy");
/// assert_eq!(sell_side.to_string(), "Sell");
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Side {
    Buy,
    Sell,
}

impl Display for Side {
    /// Implements the `fmt` method to format the `Side` enum as a string.
    ///
    /// # Arguments
    ///
    /// * `f` - A mutable reference to a `Formatter`.
    ///
    /// # Returns
    ///
    /// A result indicating success or failure.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Side::Buy => write!(f, "Buy"),
            Side::Sell => write!(f, "Sell"),
        }
    }
}

#[derive(Debug)]
pub enum UniswapEvent {
    /// The `UniswapEvent` enum represents events that can occur in the Uniswap protocol.
    /// It can either be a `Sync` event, which updates reserves, or a `Swap` event, which contains details of a swap transaction.
    ///
    /// # Examples
    ///
    /// ```
    /// use uniswapv2_vob::events::uniswap::{UniswapEvent, Side};
    /// use web3::types::{Address, U256};
    /// use rust_decimal::Decimal;
    ///
    /// let sync_event = UniswapEvent::Sync {
    ///     reserve_eth: U256::from(1000u64),
    ///     reserve_usdt: U256::from(2000u64),
    /// };
    ///
    /// let swap_event = UniswapEvent::Swap {
    ///     sender: Address::from_low_u64_be(1),
    ///     eth_in: U256::from(1u64),
    ///     usdt_in: U256::from(100u64),
    ///     eth_out: U256::from(1u64),
    ///     usdt_out: U256::from(0u64),
    ///     to: Address::from_low_u64_be(2),
    ///     effective_price: Decimal::new(100, 2),
    ///     side: Side::Buy,
    /// };
    /// ```
    Sync {
        reserve_eth: U256,
        reserve_usdt: U256,
    },
    Swap {
        sender: Address,
        eth_in: U256,
        usdt_in: U256,
        eth_out: U256,
        usdt_out: U256,
        to: Address,
        effective_price: Decimal,
        side: Side,
    },
}

/// Decodes a log event from Uniswap and returns an `UniswapEvent` if successful.
///
/// This function handles decoding two types of events: "Sync" and "Swap".
///
/// # Arguments
///
/// * `log` - A reference to a `Log` struct containing event data.
///
/// # Returns
///
/// This function returns an `Option<UniswapEvent>`. If the log matches a known event
/// type and is successfully decoded, the function returns `Some(UniswapEvent)`.
/// Otherwise, it returns `None`.
///
pub fn decode_event(log: &Log) -> Option<UniswapEvent> {
    let sync_event = Event {
        name: "Sync".to_string(),
        inputs: vec![
            EventParam {
                name: "reserve0".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
            EventParam {
                name: "reserve1".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
        ],
        anonymous: false,
    };

    let swap_event = Event {
        name: "Swap".to_string(),
        inputs: vec![
            EventParam {
                name: "sender".to_string(),
                kind: ParamType::Address,
                indexed: true,
            },
            EventParam {
                name: "amount0In".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
            EventParam {
                name: "amount1In".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
            EventParam {
                name: "amount0Out".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
            EventParam {
                name: "amount1Out".to_string(),
                kind: ParamType::Uint(256),
                indexed: false,
            },
            EventParam {
                name: "to".to_string(),
                kind: ParamType::Address,
                indexed: true,
            },
        ],
        anonymous: false,
    };

    let raw_log = RawLog {
        topics: log.topics.clone(),
        data: log.data.0.clone(),
    };

    if log.topics[0] == sync_event.signature() {
        if let Ok(decoded) = sync_event.parse_log(raw_log) {
            return Some(UniswapEvent::Sync {
                reserve_eth: decoded.params[0].value.clone().into_uint().unwrap(),
                reserve_usdt: decoded.params[1].value.clone().into_uint().unwrap(),
            });
        }
    } else if log.topics[0] == swap_event.signature() {
        if let Ok(decoded) = swap_event.parse_log(raw_log) {
            let eth_in = decoded.params[1].value.clone().into_uint().unwrap();
            let usdt_in = decoded.params[2].value.clone().into_uint().unwrap();
            let eth_out = decoded.params[3].value.clone().into_uint().unwrap();
            let usdt_out = decoded.params[4].value.clone().into_uint().unwrap();

            let effective_price = calculate_effective_price(eth_in, usdt_in, eth_out, usdt_out);

            let side = match eth_in == U256::zero() {
                true => Side::Buy,
                false => Side::Sell,
            };

            return Some(UniswapEvent::Swap {
                sender: decoded.params[0].value.clone().into_address().unwrap(),
                eth_in,
                usdt_in,
                eth_out,
                usdt_out,
                to: decoded.params[5].value.clone().into_address().unwrap(),
                effective_price,
                side,
            });
        }
    }
    None
}

/// Formats a `UniswapEvent` into a human-readable string.
///
/// This function formats both "Sync" and "Swap" events, including optional block numbers
/// and transaction hashes for context.
///
/// # Arguments
///
/// * `event` - A reference to the `UniswapEvent` to be formatted.
/// * `block_number` - An optional block number for the event.
/// * `tx_hash` - An optional transaction hash for the event.
///
/// # Returns
///
/// Returns a `String` representation of the event.
///
pub fn format_event(
    event: &UniswapEvent,
    block_number: Option<u64>,
    tx_hash: Option<web3::types::H256>,
) -> String {
    match event {
        UniswapEvent::Sync {
            reserve_eth,
            reserve_usdt,
        } => {
            format!("Sync Event (Block: {:?}, Tx: {:?}):\n  ETH Reserve: {} ETH\n  USDT Reserve: {} USDT\n  Price (USDT/ETH): {:.6} USDT/ETH",
                    block_number,
                    tx_hash,
                    format_token_amount(*reserve_eth, ETH_DECIMALS),
                    format_token_amount(*reserve_usdt, USDT_DECIMALS),
                    calculate_price(*reserve_eth, *reserve_usdt, ETH_DECIMALS, USDT_DECIMALS))
        }
        UniswapEvent::Swap {
            sender,
            eth_in,
            usdt_in,
            eth_out,
            usdt_out,
            to,
            effective_price,
            side,
        } => match *eth_in == U256::zero() {
            true => {
                format!("Swap Event (Block: {:?}, Tx: {:?}):\n\tSender: {:?}\n\tUSDT In: {} USDT\n\tETH Out: {} ETH\n\tTo: {:?}\n\tEffective Price: {:.6} ETH/USDT \n\tSide: {}",
                        block_number,
                        tx_hash,
                        sender,
                        format_token_amount(*usdt_in, USDT_DECIMALS),
                        format_token_amount(*eth_out, ETH_DECIMALS),
                        to,
                        effective_price,
                        side)
            }
            false => {
                format!("Swap Event (Block: {:?}, Tx: {:?}):\n\tSender: {:?}\n\tETH In:  {} ETH\n\tUSDT Out: {} USDT\n\tTo: {:?}\n\tEffective Price: {:.6} USDT/ETH\n\tSide: {}",
                        block_number,
                        tx_hash,
                        sender,
                        format_token_amount(*eth_in, ETH_DECIMALS),
                        format_token_amount(*usdt_out, USDT_DECIMALS),
                        to,
                        effective_price,
                        side)
            }
        },
    }
}

/// Formats a token amount with the specified number of decimals.
///
/// This function takes a raw token amount (in its smallest units) and formats it
/// into a human-readable string with the appropriate number of decimal places.
///
/// # Arguments
///
/// * `amount` - The raw token amount as a `U256`.
/// * `decimals` - The number of decimals with which to format the amount.
///
/// # Returns
///
/// Returns a `String` representation of the token amount.
/// ```
pub(crate) fn format_token_amount(amount: U256, decimals: u8) -> String {
    let decimal_factor = U256::from(10).pow(U256::from(decimals));
    let integer_part = amount / decimal_factor;
    let fractional_part = amount % decimal_factor;

    format!(
        "{}.{:0width$}",
        integer_part,
        fractional_part,
        width = decimals as usize
    )
}

/// Calculates the price based on the reserves of ETH and USDT.
///
/// # Parameters
///
/// - `reserve_eth`: The amount of ETH in the reserve as a `U256`.
/// - `reserve_usdt`: The amount of USDT in the reserve as a `U256`.
/// - `eth_decimals`: The number of decimals for ETH.
/// - `usdt_decimals`: The number of decimals for USDT.
///
/// # Returns
///
/// - Returns the price as a `f64` which is the ratio of USDT to ETH.
///
/// # Panics
///
/// - This function does not panic.
///
fn calculate_price(
    reserve_eth: U256,
    reserve_usdt: U256,
    eth_decimals: u8,
    usdt_decimals: u8,
) -> f64 {
    if reserve_eth.is_zero() {
        return 0.0;
    }
    let eth_f64 = u256_to_f64(reserve_eth, eth_decimals);
    let usdt_f64 = u256_to_f64(reserve_usdt, usdt_decimals);
    usdt_f64 / eth_f64
}

/// Calculates the effective price based on the amounts of ETH and USDT before and after a transaction.
///
/// # Parameters
///
/// - `eth_in`: The amount of ETH input as a `U256`.
/// - `usdt_in`: The amount of USDT input as a `U256`.
/// - `eth_out`: The amount of ETH output as a `U256`.
/// - `usdt_out`: The amount of USDT output as a `U256`.
///
/// # Returns
///
/// - Returns the effective price as a `Decimal`.
///
/// # Panics
///
/// - This function does not panic.
pub(crate) fn calculate_effective_price(
    eth_in: U256,
    usdt_in: U256,
    eth_out: U256,
    usdt_out: U256,
) -> Decimal {
    let eth_amount = adjust_decimals(eth_in + eth_out, ETH_DECIMALS as u32);
    let usdt_amount = adjust_decimals(usdt_in + usdt_out, USDT_DECIMALS as u32);

    if eth_amount.is_zero() && usdt_amount.is_zero() {
        warn!("Both ETH and USDT amounts are zero. Using fallback price.");
        return Decimal::new(1, 0); // Fallback to 1:1 ratio
    }

    if eth_amount.is_zero() {
        warn!("ETH amount is zero. Cannot calculate price.");
        return Decimal::MAX; // Return maximum price as we can't divide by zero
    }

    if usdt_amount.is_zero() {
        warn!("USDT amount is zero. Price is effectively zero.");
        return Decimal::new(1, 6); // Return smallest non-zero price (0.000001)
    }

    // Calculate price as USDT per ETH
    let price = usdt_amount / eth_amount;

    info!(
        "Adjusted ETH amount: {}, Adjusted USDT amount: {}, Calculated Price: {}",
        eth_amount, usdt_amount, price
    );

    // Adjust based on whether it's a buy or sell
    if !eth_in.is_zero() {
        // Buying USDT with ETH
        price
    } else {
        // Selling ETH for USDT
        Decimal::one() / price
    }
    .round_dp(6)
}

/// Converts a `U256` value to a `f64` by considering the number of decimals.
///
/// # Parameters
///
/// - `value`: The `U256` value to be converted.
/// - `decimals`: The number of decimals to consider.
///
/// # Returns
///
/// - Returns the converted value as a `f64`.
///
fn u256_to_f64(value: U256, decimals: u8) -> f64 {
    let decimal_factor = U256::from(10).pow(U256::from(decimals));
    let integer_part = value / decimal_factor;
    let fractional_part = value % decimal_factor;

    integer_part.as_u64() as f64 + (fractional_part.as_u64() as f64 / 10f64.powi(decimals as i32))
}

/// Adjusts the `U256` amount to a `Decimal` based on the number of decimals.
///
/// # Parameters
///
/// - `amount`: The `U256` amount to be adjusted.
/// - `decimals`: The number of decimals to consider.
///
/// # Returns
///
/// - Returns the adjusted amount as a `Decimal`.
fn adjust_decimals(amount: U256, decimals: u32) -> Decimal {
    let amount_decimal = u256_to_decimals(amount, 8);
    amount_decimal / Decimal::new(10_i64.pow(decimals), 0)
}

/// Creates an Ethereum-compatible event signature hash.
///
/// This function takes the name of an event and its parameters, generates a keccak256 hash,
/// and converts it into an `H256` type. It uses the `ethabi` crate to compute the event signature
/// which is required for Ethereum log decoding.
///
/// # Arguments
///
/// * `name` - A string slice that holds the name of the event.
/// * `params` - A slice of `ParamType` which describes the types of the event's parameters.
///
/// # Returns
///
/// * An `H256` type which represents the keccak256 hash of the event signature.
///
#[allow(dead_code)]
fn create_event_signature(name: &str, params: &[ParamType]) -> H256 {
    let hash = ethabi::long_signature(name, params);
    H256::from_slice(&hash.0)
}

#[cfg(test)]
mod tests_uniswap_event {
    use super::*;
    use rust_decimal::Decimal;
    use web3::types::{Address, U256};

    #[test]
    fn test_side_display() {
        assert_eq!(format!("{}", Side::Buy), "Buy");
        assert_eq!(format!("{}", Side::Sell), "Sell");
    }

    #[test]
    fn test_side_equality() {
        assert_eq!(Side::Buy, Side::Buy);
        assert_eq!(Side::Sell, Side::Sell);
        assert_ne!(Side::Buy, Side::Sell);
    }

    #[test]
    fn test_side_copy() {
        let side = Side::Buy;
        let copied_side = side;
        assert_eq!(side, copied_side);
    }

    #[test]
    fn test_uniswap_event_sync() {
        let sync_event = UniswapEvent::Sync {
            reserve_eth: U256::from(1000u64),
            reserve_usdt: U256::from(2000u64),
        };

        match sync_event {
            UniswapEvent::Sync {
                reserve_eth,
                reserve_usdt,
            } => {
                assert_eq!(reserve_eth, U256::from(1000u64));
                assert_eq!(reserve_usdt, U256::from(2000u64));
            }
            _ => panic!("Expected Sync event"),
        }
    }

    #[test]
    fn test_uniswap_event_swap() {
        let swap_event = UniswapEvent::Swap {
            sender: Address::from_low_u64_be(1),
            eth_in: U256::from(1u64),
            usdt_in: U256::from(100u64),
            eth_out: U256::from(0u64),
            usdt_out: U256::from(0u64),
            to: Address::from_low_u64_be(2),
            effective_price: Decimal::new(100, 0),
            side: Side::Buy,
        };

        match swap_event {
            UniswapEvent::Swap {
                sender,
                eth_in,
                usdt_in,
                eth_out,
                usdt_out,
                to,
                effective_price,
                side,
            } => {
                assert_eq!(sender, Address::from_low_u64_be(1));
                assert_eq!(eth_in, U256::from(1u64));
                assert_eq!(usdt_in, U256::from(100u64));
                assert_eq!(eth_out, U256::from(0u64));
                assert_eq!(usdt_out, U256::from(0u64));
                assert_eq!(to, Address::from_low_u64_be(2));
                assert_eq!(effective_price, Decimal::new(100, 0));
                assert_eq!(side, Side::Buy);
            }
            _ => panic!("Expected Swap event"),
        }
    }

    #[test]
    fn test_uniswap_event_debug() {
        let sync_event = UniswapEvent::Sync {
            reserve_eth: U256::from(1000u64),
            reserve_usdt: U256::from(2000u64),
        };
        let debug_output = format!("{:?}", sync_event);
        assert!(debug_output.contains("Sync"));
        assert!(debug_output.contains("1000"));
        assert!(debug_output.contains("2000"));

        let swap_event = UniswapEvent::Swap {
            sender: Address::from_low_u64_be(1),
            eth_in: U256::from(1u64),
            usdt_in: U256::from(100u64),
            eth_out: U256::from(0u64),
            usdt_out: U256::from(0u64),
            to: Address::from_low_u64_be(2),
            effective_price: Decimal::new(100, 0),
            side: Side::Buy,
        };
        let debug_output = format!("{:?}", swap_event);
        assert!(debug_output.contains("Swap"));
        assert!(debug_output.contains("Buy"));
    }
}

#[cfg(test)]
mod tests_decode_event {
    use super::*;
    use ethabi::Token;
    use web3::types::{Address, Bytes, Log, U256};

    fn create_log(topics: Vec<H256>, data: Vec<u8>) -> Log {
        Log {
            address: Address::zero(),
            topics,
            data: Bytes(data),
            block_hash: None,
            block_number: None,
            transaction_hash: None,
            transaction_index: None,
            log_index: None,
            transaction_log_index: None,
            log_type: None,
            removed: None,
        }
    }

    #[test]
    fn test_decode_sync_event() {
        let sync_signature =
            create_event_signature("Sync", &[ParamType::Uint(256), ParamType::Uint(256)]);

        let log = create_log(
            vec![sync_signature],
            ethabi::encode(&[
                Token::Uint(U256::from(1000)), // reserve_eth
                Token::Uint(U256::from(2000)), // reserve_usdt
            ]),
        );

        let decoded = decode_event(&log);
        assert!(decoded.is_some());

        if let Some(UniswapEvent::Sync {
            reserve_eth,
            reserve_usdt,
        }) = decoded
        {
            assert_eq!(reserve_eth, U256::from(1000));
            assert_eq!(reserve_usdt, U256::from(2000));
        } else {
            panic!("Expected Sync event");
        }
    }

    #[test]
    fn test_decode_swap_event() {
        let swap_signature = create_event_signature(
            "Swap",
            &[
                ParamType::Address,
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Address,
            ],
        );

        let sender = Address::from_low_u64_be(1);
        let to = Address::from_low_u64_be(2);

        let log = create_log(
            vec![swap_signature, H256::from(sender), H256::from(to)],
            ethabi::encode(&[
                Token::Uint(U256::from(100)), // eth_in
                Token::Uint(U256::from(0)),   // usdt_in
                Token::Uint(U256::from(0)),   // eth_out
                Token::Uint(U256::from(200)), // usdt_out
            ]),
        );

        let decoded = decode_event(&log);
        assert!(decoded.is_some());

        if let Some(UniswapEvent::Swap {
            sender: s,
            eth_in,
            usdt_in,
            eth_out,
            usdt_out,
            to: t,
            effective_price: _,
            side,
        }) = decoded
        {
            assert_eq!(s, sender);
            assert_eq!(t, to);
            assert_eq!(eth_in, U256::from(100));
            assert_eq!(usdt_in, U256::from(0));
            assert_eq!(eth_out, U256::from(0));
            assert_eq!(usdt_out, U256::from(200));
            assert_eq!(side, Side::Sell);
            // Note: We're not checking effective_price here as it depends on calculate_effective_price function
        } else {
            panic!("Expected Swap event");
        }
    }

    #[test]
    fn test_decode_unknown_event() {
        let unknown_signature = H256::random();
        let log = create_log(vec![unknown_signature], vec![]);

        let decoded = decode_event(&log);
        assert!(decoded.is_none());
    }

    #[test]
    fn test_decode_malformed_sync_event() {
        let sync_signature =
            create_event_signature("Sync", &[ParamType::Uint(256), ParamType::Uint(256)]);

        let log = create_log(
            vec![sync_signature],
            ethabi::encode(&[
                Token::Uint(U256::from(1000)),
                // Missing second parameter
            ]),
        );

        let decoded = decode_event(&log);
        assert!(decoded.is_none());
    }

    #[test]
    fn test_decode_malformed_swap_event() {
        let swap_signature = create_event_signature(
            "Swap",
            &[
                ParamType::Address,
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Uint(256),
                ParamType::Address,
            ],
        );

        let log = create_log(
            vec![swap_signature],
            ethabi::encode(&[
                Token::Address(Address::zero()),
                Token::Uint(U256::from(100)),
                Token::Uint(U256::from(0)),
                Token::Uint(U256::from(0)),
                // Missing last two parameters
            ]),
        );

        let decoded = decode_event(&log);
        assert!(decoded.is_none());
    }
}

#[cfg(test)]
mod tests_format_event {
    use super::*;
    use web3::types::{H256, U256};

    #[test]
    fn test_format_sync_event_with_block_and_tx() {
        let event = UniswapEvent::Sync {
            reserve_eth: U256::from(100_000_000_000_000_000u64),
            reserve_usdt: U256::from(200_000_000u64),
        };
        let block_number = Some(12345678);
        let tx_hash = Some(H256::random());

        let result = format_event(&event, block_number, tx_hash);

        assert!(result.contains("Sync Event"));
        assert!(result.contains("Block: Some(12345678)"));
        assert!(result.contains("ETH Reserve: 0.100000000000000000 ETH"));
        assert!(result.contains("USDT Reserve: 200.0 USDT"));
        assert!(result.contains("Price (USDT/ETH): 2000.000000 USDT/ETH"));
    }

    #[test]
    fn test_format_sync_event_without_block_and_tx() {
        let event = UniswapEvent::Sync {
            reserve_eth: U256::from(50_000_000_000_000_000u64),
            reserve_usdt: U256::from(100_000_000u64),
        };

        let result = format_event(&event, None, None);
        println!("{}", result);
        assert!(result.contains("Sync Event"));
        assert!(result.contains("Block: None"));
        assert!(result.contains("Tx: None"));
        assert!(result.contains("ETH Reserve: 0.050000000000000000 ETH"));
        assert!(result.contains("USDT Reserve: 100.0 USDT"));
        assert!(result.contains("Price (USDT/ETH): 2000.000000 USDT/ETH"));
    }
}

#[cfg(test)]
mod tests_format_token_amount {
    use super::*;

    #[test]
    fn test_format_token_amount_whole_number() {
        let amount = U256::from(1000000000000000000u64); // 1 ETH
        assert_eq!(format_token_amount(amount, 18), "1.0");
    }

    #[test]
    fn test_format_token_amount_fractional() {
        let amount = U256::from(123450000000000000u64); // 0.12345 ETH
        assert_eq!(format_token_amount(amount, 18), "0.123450000000000000");
    }

    #[test]
    fn test_format_token_amount_zero() {
        let amount = U256::zero();
        assert_eq!(format_token_amount(amount, 18), "0.0");
    }

    #[test]
    fn test_format_token_amount_large_number() {
        let amount = U256::from_dec_str("123456789000000000000000000").unwrap(); // 123,456,789 ETH
        assert_eq!(format_token_amount(amount, 18), "123456789.0");
    }

    #[test]
    fn test_format_token_amount_small_decimals() {
        let amount = U256::from(1234567u64); // 1.234567 USDT (6 decimals)
        assert_eq!(format_token_amount(amount, 6), "1.234567");
    }

    #[test]
    fn test_format_token_amount_no_decimals() {
        let amount = U256::from(1234u64);
        assert_eq!(format_token_amount(amount, 0), "1234.0");
    }

    #[test]
    fn test_format_token_amount_max_value() {
        let amount = U256::max_value();
        let formatted = format_token_amount(amount, 18);
        assert!(
            formatted.starts_with("115792089237316195423570985008687907853269984665640564039457")
        );
        assert_eq!(formatted.len(), 79); // 1 (dot) + 18 (decimals) + 59 (digits before dot)
    }
}

#[cfg(test)]
mod tests_calculate_price {
    use super::*;
    use web3::types::U256;

    #[test]
    fn test_calculate_price_normal_case() {
        let reserve_eth = U256::from(10_000_000_000_000_000u64); // 0.01 ETH
        let reserve_usdt = U256::from(20_000_000u64); // 20 USDT
        let eth_decimals = 18;
        let usdt_decimals = 6;

        let price = calculate_price(reserve_eth, reserve_usdt, eth_decimals, usdt_decimals);
        assert_eq!(price, 2000.0);
    }

    #[test]
    fn test_calculate_price_eth_zero() {
        let reserve_eth = U256::zero(); // 0 ETH
        let reserve_usdt = U256::from(10_000_000u64); // 10 USDT
        let eth_decimals = 18;
        let usdt_decimals = 6;

        let price = calculate_price(reserve_eth, reserve_usdt, eth_decimals, usdt_decimals);
        assert_eq!(price, 0.0); // Si no hay ETH en la reserva, el precio es 0
    }

    #[test]
    fn test_calculate_price_usdt_zero() {
        let reserve_eth = U256::from(1_000_000_000_000_000_000u64); // 1 ETH
        let reserve_usdt = U256::zero(); // 0 USDT
        let eth_decimals = 18;
        let usdt_decimals = 6;

        let price = calculate_price(reserve_eth, reserve_usdt, eth_decimals, usdt_decimals);
        assert_eq!(price, 0.0); // Si no hay USDT en la reserva, el precio es 0
    }

    #[test]
    fn test_calculate_price_large_values() {
        let reserve_eth = U256::from(1_000_000_000_000_000_000u64); // 1 ETH
        let reserve_usdt = U256::from(2_000_000_000_000u64); // 2,000,000 USDT
        let eth_decimals = 18;
        let usdt_decimals = 6;

        let price = calculate_price(reserve_eth, reserve_usdt, eth_decimals, usdt_decimals);
        assert_eq!(price, 2_000_000.0); // El precio debería ser 2,000,000 USDT por ETH
    }

    #[test]
    fn test_calculate_price_different_decimals() {
        let reserve_eth = U256::from(10_000_000_000_000_000u64); // 0.01 ETH
        let reserve_usdt = U256::from(20_000_000_000_000u64); // 20,000 USDT (con más decimales)
        let eth_decimals = 18;
        let usdt_decimals = 12;

        let price = calculate_price(reserve_eth, reserve_usdt, eth_decimals, usdt_decimals);
        assert_eq!(price, 2_000.0); // El precio es 2,000,000 USDT por ETH
    }
}

#[cfg(test)]
mod tests_calculate_effective_price {
    use super::*;
    use crate::utils::logger::setup_logger;
    use rust_decimal_macros::dec;

    #[test]
    fn test_calculate_effective_price_buy_eth() {
        setup_logger();
        let eth_in = U256::zero();
        let usdt_in = U256::from(2000_000000); // 2000 USDT
        let eth_out = U256::from(1_000000000000000000u64); // 1 ETH
        let usdt_out = U256::zero();

        let price = calculate_effective_price(eth_in, usdt_in, eth_out, usdt_out);
        assert_eq!(price, dec!(0.0005));
    }

    #[test]
    fn test_calculate_effective_price_sell_eth() {
        setup_logger();
        let eth_in = U256::from(1_000000000000000000u64); // 1 ETH
        let usdt_in = U256::zero();
        let eth_out = U256::zero();
        let usdt_out = U256::from(2000_000000); // 2000 USDT

        let price = calculate_effective_price(eth_in, usdt_in, eth_out, usdt_out);
        assert_eq!(price, dec!(2000.000000));
    }

    #[test]
    fn test_calculate_effective_price_both_zero() {
        setup_logger();

        let price =
            calculate_effective_price(U256::zero(), U256::zero(), U256::zero(), U256::zero());
        assert_eq!(price, dec!(1));
    }

    #[test]
    fn test_calculate_effective_price_eth_zero() {
        setup_logger();

        let price = calculate_effective_price(
            U256::zero(),
            U256::from(1000_000000),
            U256::zero(),
            U256::zero(),
        );
        assert_eq!(price, Decimal::MAX);
    }

    #[test]
    fn test_calculate_effective_price_usdt_zero() {
        setup_logger();

        let price = calculate_effective_price(
            U256::from(1_000000000000000000u64),
            U256::zero(),
            U256::zero(),
            U256::zero(),
        );
        assert_eq!(price, dec!(0.000001));
    }

    #[test]
    fn test_calculate_effective_price_large_numbers() {
        setup_logger();
        let eth_in = U256::from(1000_000000000000000000u128); // 1000 ETH
        let usdt_in = U256::zero();
        let eth_out = U256::zero();
        let usdt_out = U256::from(3_000_000_000_000_u128); // 3,000,000 USDT

        let price = calculate_effective_price(eth_in, usdt_in, eth_out, usdt_out);
        assert_eq!(price, dec!(3000.000000));
    }

    #[test]
    fn test_calculate_effective_price_small_numbers() {
        setup_logger();
        let eth_in = U256::from(1000000000000000u64); // 0.001 ETH
        let usdt_in = U256::zero();
        let eth_out = U256::zero();
        let usdt_out = U256::from(2_000000); // 2 USDT

        let price = calculate_effective_price(eth_in, usdt_in, eth_out, usdt_out);
        assert_eq!(price, dec!(2000.000000));
    }
}

#[cfg(test)]
mod tests_u256_to_f64 {
    use super::*;
    use web3::types::U256;

    #[test]
    fn test_u256_to_f64_whole_number() {
        let value = U256::from(1_000_000_000_000_000_000u64); // 1 ETH con 18 decimales
        let decimals = 18;

        let result = u256_to_f64(value, decimals);
        assert_eq!(result, 1.0);
    }

    #[test]
    fn test_u256_to_f64_fractional_number() {
        let value = U256::from(500_000_000_000_000u64); // 0.5 ETH con 18 decimales
        let decimals = 18;

        let result = u256_to_f64(value, decimals);

        assert!((result - 0.0005).abs() < 1e-9);
    }

    #[test]
    fn test_u256_to_f64_large_number() {
        let value = U256::from(2_000_000_000_000_000_000u64); // 2 ETH con 18 decimales
        let decimals = 18;

        let result = u256_to_f64(value, decimals);
        assert_eq!(result, 2.0);
    }

    #[test]
    fn test_u256_to_f64_small_fraction() {
        let value = U256::from(1_000u64); // 0.000000000000001 ETH con 18 decimales
        let decimals = 18;

        let result = u256_to_f64(value, decimals);
        assert!((result - 0.000000000000001).abs() < 1e-18);
    }

    #[test]
    fn test_u256_to_f64_zero_value() {
        let value = U256::zero(); // 0 ETH
        let decimals = 18;

        let result = u256_to_f64(value, decimals);
        assert_eq!(result, 0.0);
    }

    #[test]
    fn test_u256_to_f64_different_decimals() {
        let value = U256::from(123_456_000_000u64); // 123.456 USDT con 6 decimales
        let decimals = 6;

        let result = u256_to_f64(value, decimals);
        println!("{}", result);
        assert!((result - 123456.0).abs() < 1e-6);
    }
}

#[cfg(test)]
mod tests_adjust_decimals {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_adjust_decimals_no_adjustment() {
        let amount = U256::from(1000000000000000000u64); // 1 ETH
        let result = adjust_decimals(amount, 0);
        assert_eq!(result, dec!(10000000000.00000000));
    }

    #[test]
    fn test_adjust_decimals_18_decimals() {
        let amount = U256::from(1000000000000000000u64); // 1 ETH
        let result = adjust_decimals(amount, 18);
        assert_eq!(result, dec!(0.00000001));
    }

    #[test]
    fn test_adjust_decimals_6_decimals() {
        let amount = U256::from(1000000u64); // 1 USDT
        let result = adjust_decimals(amount, 6);
        assert_eq!(result, dec!(0.00000001));
    }

    #[test]
    fn test_adjust_decimals_large_number() {
        let amount = U256::from(1000000000000000000000u128); // 1000 ETH
        let result = adjust_decimals(amount, 18);
        assert_eq!(result, dec!(0.00001000));
    }

    #[test]
    fn test_adjust_decimals_small_number() {
        let amount = U256::from(1u64); // Smallest non-zero amount
        let result = adjust_decimals(amount, 18);
        assert_eq!(result, dec!(0.00000000000000000000000001));
    }

    #[test]
    fn test_adjust_decimals_zero() {
        let amount = U256::zero();
        let result = adjust_decimals(amount, 18);
        assert_eq!(result, dec!(0));
    }

    #[test]
    fn test_adjust_decimals_eth_to_usdt() {
        let amount = U256::from(150000000000000000000u128); // 1.5 ETH
        let result = adjust_decimals(amount, 12); // Adjust from 18 to 6 decimals
        assert_eq!(result, dec!(1.5));
    }

    #[test]
    fn test_adjust_decimals_usdt_to_eth() {
        let amount = U256::from(250000000u64); // 2.5 USDT
        let result = adjust_decimals(amount, 0); // No adjustment needed
        assert_eq!(result, dec!(2.500000));
    }

    #[test]
    fn test_adjust_decimals_fractional_eth() {
        let amount = U256::from(123456789012345678u128);
        let result = adjust_decimals(amount, 18);
        assert_eq!(result, dec!(0.00000000123456789012345678));
    }
}
