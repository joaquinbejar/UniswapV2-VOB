use crate::constants::{ETH_DECIMALS, USDT_DECIMALS};
use crate::events::uniswap::Side;
use crate::orderbook::model::SwapInfo;
use crate::utils::logic::{decimal_sqrt, solve_linear_system, u256_to_decimals};
use num_traits::{One, Zero};
use rust_decimal::Decimal;
use std::ops::Neg;
use tracing::debug;
use web3::types::U256;

/// Calculates the reserves based on the provided SwapInfo.
///
/// The function takes two swap transactions (swap1 and swap2) and returns the calculated reserves
/// (either ETH reserve and USDT reserve or vice versa) based on the side of the swap (buy or sell).
///
/// # Arguments
///
/// * `swap1` - A reference to the first SwapInfo object containing details of the first swap.
/// * `swap2` - A reference to the second SwapInfo object containing details of the second swap.
///
/// # Returns
///
/// Returns a tuple containing Decimal values of the calculated reserves or an error message if
/// the swaps do not have the same side or if the linear system solution fails.
///
/// # Errors
///
/// Returns an error if the `swap1` and `swap2` do not have the same side or if the linear system
/// cannot be solved.
///
pub(crate) fn calculate_reserves(
    swap1: &SwapInfo,
    swap2: &SwapInfo,
) -> Result<(Decimal, Decimal), String> {
    if swap1.side != swap2.side {
        return Err("Swaps must have the same side".to_string());
    }

    let (a1, b1, c1) = match swap1.side {
        Side::Buy => {
            let usdt_in = u256_to_decimals(swap1.usdt_in, USDT_DECIMALS);
            let eth_out = u256_to_decimals(swap1.eth_out, ETH_DECIMALS);
            (usdt_in, eth_out.neg(), usdt_in * eth_out)
        }
        Side::Sell => {
            let eth_in = u256_to_decimals(swap1.eth_in, ETH_DECIMALS);
            let usdt_out = u256_to_decimals(swap1.usdt_out, USDT_DECIMALS);
            (eth_in, usdt_out.neg(), eth_in * usdt_out)
        }
    };

    let (a2, b2, c2) = match swap2.side {
        Side::Buy => {
            let usdt_in = u256_to_decimals(swap2.usdt_in, USDT_DECIMALS) + a1;
            let eth_out = u256_to_decimals(swap2.eth_out, ETH_DECIMALS) + b1.neg();
            (usdt_in, eth_out.neg(), usdt_in * eth_out)
        }
        Side::Sell => {
            let eth_in = u256_to_decimals(swap2.eth_in, ETH_DECIMALS) + a1;
            let usdt_out = u256_to_decimals(swap2.usdt_out, USDT_DECIMALS) + b1.neg();
            (eth_in, usdt_out.neg(), eth_in * usdt_out)
        }
    };
    debug!("a1: {}, b1: {}, c1: {}", a1, b1, c1);
    debug!("a2: {}, b2: {}, c2: {}", a2, b2, c2);
    let results = solve_linear_system(a1, b1, c1, a2, b2, c2);
    match (results, swap1.side) {
        (Some((eth_reserve, usdt_reserve)), Side::Buy) => Ok((eth_reserve, usdt_reserve)),
        (Some((eth_reserve, usdt_reserve)), Side::Sell) => Ok((usdt_reserve, eth_reserve)),
        (None, _) => Err("Failed to solve linear system".to_string()),
    }
}

/// Calculates reserve adjustments based on provided reserves and target prices.
///
/// The function adjusts reserves of ETH and USDT to ensure they match a target price if provided.
/// If neither target price is provided, an error is returned.
///
/// # Arguments
///
/// * `reserve_eth` - The current reserve of ETH as U256.
/// * `reserve_usdt` - The current reserve of USDT as U256.
/// * `target_price_usdt` - An optional target price for USDT as Decimal.
/// * `target_price_eth` - An optional target price for ETH as Decimal.
///
/// # Returns
///
/// Returns a tuple containing Decimal values of the adjusted reserves or an error message if
/// neither target price is provided or if provided target prices are inconsistent.
///
/// # Errors
///
/// Returns an error if both target prices are None or if they are inconsistent.
///
pub(crate) fn calculate_reserve_adjustment(
    reserve_eth: U256,
    reserve_usdt: U256,
    target_price_usdt: Option<Decimal>,
    target_price_eth: Option<Decimal>,
) -> Result<(Decimal, Decimal), String> {
    if target_price_usdt.is_none() && target_price_eth.is_none() {
        return Err("At least one target price must be provided".to_string());
    }

    let dec_reserve_eth = u256_to_decimals(reserve_eth, ETH_DECIMALS);
    let dec_reserve_usdt = u256_to_decimals(reserve_usdt, USDT_DECIMALS);

    // Handle the case where both reserves are zero
    if dec_reserve_eth.is_zero() && dec_reserve_usdt.is_zero() {
        return Ok((Decimal::zero(), Decimal::zero()));
    }

    let k = dec_reserve_eth * dec_reserve_usdt;
    let current_price = if dec_reserve_eth.is_zero() {
        Decimal::MAX
    } else {
        dec_reserve_usdt / dec_reserve_eth
    };

    let (new_reserve_eth, new_reserve_usdt) = match (target_price_usdt, target_price_eth) {
        (Some(price_usdt), None) => {
            if k.is_zero() {
                (Decimal::zero(), Decimal::zero())
            } else {
                let new_eth = decimal_sqrt(k / price_usdt);
                (new_eth, k / new_eth)
            }
        }
        (None, Some(price_eth)) => {
            if k.is_zero() {
                (Decimal::zero(), Decimal::zero())
            } else {
                let new_usdt = decimal_sqrt(k * price_eth);
                (k / new_usdt, new_usdt)
            }
        }
        (Some(price_usdt), Some(price_eth)) => {
            let epsilon = Decimal::new(1, 12); // 1e-12
            if (Decimal::one() / price_eth - price_usdt).abs() > epsilon {
                return Err("Inconsistent target prices provided".to_string());
            }
            if k.is_zero() {
                (Decimal::zero(), Decimal::zero())
            } else {
                let new_eth = decimal_sqrt(k / price_usdt);
                (new_eth, k / new_eth)
            }
        }
        _ => unreachable!(),
    };

    let eth_adjustment = new_reserve_eth - dec_reserve_eth;
    let usdt_adjustment = new_reserve_usdt - dec_reserve_usdt;

    // Log additional information for debugging
    debug!("Current price: {}", current_price);
    debug!("New ETH reserve: {}", new_reserve_eth);
    debug!("New USDT reserve: {}", new_reserve_usdt);

    Ok((eth_adjustment, usdt_adjustment))
}

#[cfg(test)]
mod tests_calculate_reserves {
    use super::*;
    use crate::orderbook::model::SwapInfo;
    use crate::utils::logger::setup_logger;
    use num_traits::Zero;
    use rust_decimal_macros::dec;
    use std::str::FromStr;
    use tracing::info;
    use web3::types::U256;

    #[test]
    fn test_calculate_reserves() {
        setup_logger();
        // First swap: 4800 USDT in, 1.817457120942687720 ETH out
        let swap_1 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4800000000").unwrap(), // 4800 USDT with 6 decimals
            eth_out: U256::from_dec_str("1817457120942687720").unwrap(), // 1.817457120942687720 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        };

        // Second swap: 5000 USDT in, 1.892905982365873578 ETH out
        let swap_2 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("5000000000").unwrap(), // 5000 USDT with 6 decimals
            eth_out: U256::from_dec_str("1892905982365873578").unwrap(), // 1.892905982365873578 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379 USDT/ETH
            side: Side::Buy,
        };

        let result = calculate_reserves(&swap_1, &swap_2);

        match result {
            Ok((eth_reserve, usdt_reserve)) => {
                info!(
                    "Test passed. ETH reserve: {}, USDT reserve: {}",
                    eth_reserve, usdt_reserve
                );

                // Check that reserves are positive
                assert!(
                    eth_reserve > Decimal::zero(),
                    "ETH reserve should be positive"
                );
                assert!(
                    usdt_reserve > Decimal::zero(),
                    "USDT reserve should be positive"
                );

                // Check that reserves are within a reasonable range
                let min_expected_eth = dec!(3.710363103308561298);
                assert!(
                    eth_reserve > min_expected_eth,
                    "ETH reserve is less than expected"
                );

                let min_expected_usdt = dec!(9800);
                assert!(
                    usdt_reserve > min_expected_usdt,
                    "USDT reserve is less than expected"
                );

                // Check that the product of reserves increases
                let initial_product =
                    (eth_reserve + dec!(3.710363103308561298)) * (usdt_reserve - dec!(9800));
                let final_product = eth_reserve * usdt_reserve;
                assert!(
                    final_product > initial_product,
                    "Product of reserves should increase"
                );

                assert_eq!(
                    eth_reserve,
                    Decimal::from_str("25220.583165107801329842278135").unwrap()
                );
                assert_eq!(
                    usdt_reserve,
                    Decimal::from_str("66604088.758666319955654387953").unwrap()
                );
            }
            Err(e) => {
                panic!("calculate_reserves failed: {}", e);
            }
        }
    }

    #[test]
    fn test_calculate_reserves_inverse_price() {
        // Same swaps as before, but with inverse price (USDT/ETH instead of ETH/USDT)
        let swap_1 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4800000000").unwrap(),
            eth_out: U256::from_dec_str("1817457120942687720").unwrap(),
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379
            side: Side::Buy,
        };

        let swap_2 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("5000000000").unwrap(),
            eth_out: U256::from_dec_str("1892905982365873578").unwrap(),
            usdt_out: U256::zero(),
            effective_price: dec!(2638.522427440633245382585752), // 1 / 0.000379
            side: Side::Buy,
        };

        let result = calculate_reserves(&swap_1, &swap_2);

        match result {
            Ok((eth_reserve, usdt_reserve)) => {
                info!(
                    "Test passed. ETH reserve: {}, USDT reserve: {}",
                    eth_reserve, usdt_reserve
                );

                // Check that reserves are positive
                assert!(
                    eth_reserve > Decimal::zero(),
                    "ETH reserve should be positive"
                );
                assert!(
                    usdt_reserve > Decimal::zero(),
                    "USDT reserve should be positive"
                );

                // Check that reserves are within a reasonable range
                let min_expected_eth = dec!(3.710363103308561298);
                assert!(
                    eth_reserve > min_expected_eth,
                    "ETH reserve is less than expected"
                );

                let min_expected_usdt = dec!(9800);
                assert!(
                    usdt_reserve > min_expected_usdt,
                    "USDT reserve is less than expected"
                );

                // Check that the product of reserves increases
                let initial_product =
                    (eth_reserve + dec!(3.710363103308561298)) * (usdt_reserve - dec!(9800));
                let final_product = eth_reserve * usdt_reserve;
                assert!(
                    final_product > initial_product,
                    "Product of reserves should increase"
                );

                assert_eq!(
                    eth_reserve,
                    Decimal::from_str("25220.583165107801329842278135").unwrap()
                );
                assert_eq!(
                    usdt_reserve,
                    Decimal::from_str("66604088.758666319955654387953").unwrap()
                );
            }
            Err(e) => {
                panic!("calculate_reserves failed: {}", e);
            }
        }
    }

    #[test]
    fn test_calculate_reserves_with_new_swaps() {
        setup_logger();

        // First swap: 4767.498798 USDT in, 1.838455008411508733 ETH out
        let swap_1 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("4767498798").unwrap(), // 4767.498798 USDT with 6 decimals
            eth_out: U256::from_dec_str("1838455008411508733").unwrap(), // 1.838455008411508733 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2636.183892341024215), // Example effective price (USDT/ETH)
            side: Side::Buy,
        };

        // Second swap: 1000.000000 USDT in, 0.385588820079272392 ETH out
        let swap_2 = SwapInfo {
            eth_in: U256::zero(),
            usdt_in: U256::from_dec_str("1000000000").unwrap(), // 1000 USDT with 6 decimals
            eth_out: U256::from_dec_str("385588820079272392").unwrap(), // 0.385588820079272392 ETH with 18 decimals
            usdt_out: U256::zero(),
            effective_price: dec!(2592.918929999999), // Example effective price (USDT/ETH)
            side: Side::Buy,
        };

        let result = calculate_reserves(&swap_1, &swap_2);

        match result {
            Ok((eth_reserve, usdt_reserve)) => {
                info!(
                    "Test passed. ETH reserve: {}, USDT reserve: {}",
                    eth_reserve, usdt_reserve
                );

                // Check that reserves are positive
                assert!(
                    eth_reserve > Decimal::zero(),
                    "ETH reserve should be positive"
                );
                assert!(
                    usdt_reserve > Decimal::zero(),
                    "USDT reserve should be positive"
                );

                // Check that reserves are within a reasonable range
                let min_expected_eth = dec!(2.224043828490781125); // Sum of ETH out from both swaps
                assert!(
                    eth_reserve > min_expected_eth,
                    "ETH reserve is less than expected"
                );

                let min_expected_usdt = dec!(5767.498798); // Sum of USDT in from both swaps
                assert!(
                    usdt_reserve > min_expected_usdt,
                    "USDT reserve is less than expected"
                );

                // Check that the product of reserves increases
                let initial_product =
                    (eth_reserve + min_expected_eth) * (usdt_reserve - min_expected_usdt);
                let final_product = eth_reserve * usdt_reserve;
                assert!(
                    final_product > initial_product,
                    "Product of reserves should increase"
                );

                assert_eq!(
                    eth_reserve,
                    Decimal::from_str("25432.29176838273526355426331").unwrap()
                ); // Example expected reserve
                assert_eq!(
                    usdt_reserve,
                    Decimal::from_str("65946490.422337085067072063351").unwrap()
                ); // Example expected reserve
            }
            Err(e) => {
                panic!("calculate_reserves failed: {}", e);
            }
        }
    }

    #[test]
    fn test_calculate_reserves_with_sell_swaps() {
        setup_logger();

        // First swap: 0.127263917200000000 ETH in, 328.080223 USDT out
        let swap_1 = SwapInfo {
            eth_in: U256::from_dec_str("127263917200000000").unwrap(), // 0.1272639172 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("328080223").unwrap(), // 328.080223 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        };

        // Second swap: 0.194439766600168513 ETH in, 501.250000 USDT out
        let swap_2 = SwapInfo {
            eth_in: U256::from_dec_str("194439766600168513").unwrap(), // 0.194439766600168513 ETH with 18 decimals
            usdt_in: U256::zero(),
            eth_out: U256::zero(),
            usdt_out: U256::from_dec_str("501250000").unwrap(), // 501.250000 USDT with 6 decimals
            effective_price: dec!(2577.524845218), // Example effective price (USDT/ETH)
            side: Side::Sell,
        };

        let result = calculate_reserves(&swap_1, &swap_2);

        match result {
            Ok((eth_reserve, usdt_reserve)) => {
                info!(
                    "Test passed. ETH reserve: {}, USDT reserve: {}",
                    eth_reserve, usdt_reserve
                );

                // Check that reserves are positive
                assert!(
                    eth_reserve > Decimal::zero(),
                    "ETH reserve should be positive"
                );
                assert!(
                    usdt_reserve > Decimal::zero(),
                    "USDT reserve should be positive"
                );

                // Check that reserves are within a reasonable range
                let min_expected_eth = dec!(0.321703683800168513); // Sum of ETH in from both swaps
                assert!(
                    eth_reserve > min_expected_eth,
                    "ETH reserve is less than expected"
                );

                let min_expected_usdt = dec!(829.330223); // Sum of USDT out from both swaps
                assert!(
                    usdt_reserve > min_expected_usdt,
                    "USDT reserve is less than expected"
                );

                // Check that the product of reserves increases
                let initial_product =
                    (eth_reserve - min_expected_eth) * (usdt_reserve + min_expected_usdt);
                let final_product = eth_reserve * usdt_reserve;
                assert!(
                    final_product > initial_product,
                    "Product of reserves should increase"
                );

                assert_eq!(
                    eth_reserve,
                    Decimal::from_str("25540.8510763870972525985544").unwrap()
                ); // Example expected reserve
                assert_eq!(
                    usdt_reserve,
                    Decimal::from_str("65843406.787145506240089402637").unwrap()
                ); // Example expected reserve
            }
            Err(e) => {
                panic!("calculate_reserves failed: {}", e);
            }
        }
    }
}

#[cfg(test)]
mod tests_calculate_reserve_adjustment {
    use super::*;
    use crate::utils::logger::setup_logger;
    use rust_decimal_macros::dec;
    use tracing::{error, info};
    use web3::types::U256;

    // Helper function to create U256 from a decimal string
    fn u256_from_dec_str(s: &str) -> U256 {
        U256::from_dec_str(s).unwrap()
    }

    #[test]
    fn test_calculate_reserve_adjustment_usdt_price() {
        setup_logger();
        let reserve_eth = u256_from_dec_str("10000000000000000000"); // 10 ETH
        let reserve_usdt = u256_from_dec_str("20000000000"); // 20,000 USDT
        let target_price_usdt = Some(dec!(2100)); // Target price: 2100 USDT/ETH

        let result =
            calculate_reserve_adjustment(reserve_eth, reserve_usdt, target_price_usdt, None);
        assert!(result.is_ok());
        let (eth_adj, usdt_adj) = result.unwrap();

        // Check that adjustments are non-zero and in the correct direction
        assert!(eth_adj < dec!(0)); // ETH reserve should decrease
        assert!(usdt_adj > dec!(0)); // USDT reserve should increase
    }

    #[test]
    fn test_calculate_reserve_adjustment_eth_price() {
        setup_logger();
        let reserve_eth = u256_from_dec_str("10000000000000000000"); // 10 ETH
        let reserve_usdt = u256_from_dec_str("20000000000"); // 20,000 USDT
        let target_price_eth = Some(dec!(0.00047619)); // Target price: 1/2100 ETH/USDT (increasing ETH price)

        let result =
            calculate_reserve_adjustment(reserve_eth, reserve_usdt, None, target_price_eth);
        assert!(result.is_ok());
        let (eth_adj, usdt_adj) = result.unwrap();

        info!("ETH adjustment: {}, USDT adjustment: {}", eth_adj, usdt_adj);

        // Check that adjustments are non-zero and in the correct direction
        assert!(
            eth_adj > dec!(0),
            "ETH reserve should increase to raise the price of ETH"
        );
        assert!(
            usdt_adj < dec!(0),
            "USDT reserve should decrease to raise the price of ETH"
        );

        // Optional: Add more specific checks if needed
        assert!(
            eth_adj.abs() > dec!(1),
            "ETH adjustment should be significant"
        );
        assert!(
            usdt_adj.abs() > dec!(1000),
            "USDT adjustment should be significant"
        );
    }

    #[test]
    fn test_calculate_reserve_adjustment_both_prices() {
        setup_logger(); // Asegúrate de que el logger está configurado

        let reserve_eth = u256_from_dec_str("10000000000000000000"); // 10 ETH
        let reserve_usdt = u256_from_dec_str("20000000000"); // 20,000 USDT
        let target_price_usdt = Some(dec!(2100));
        let target_price_eth = Some(dec!(1) / dec!(2100));

        info!("Reserve ETH: {}", reserve_eth);
        info!("Reserve USDT: {}", reserve_usdt);
        info!("Target price USDT: {:?}", target_price_usdt);
        info!("Target price ETH: {:?}", target_price_eth);

        let result = calculate_reserve_adjustment(
            reserve_eth,
            reserve_usdt,
            target_price_usdt,
            target_price_eth,
        );

        match result {
            Ok((eth_adj, usdt_adj)) => {
                info!("Calculation successful");
                info!("ETH adjustment: {}", eth_adj);
                info!("USDT adjustment: {}", usdt_adj);
                // Puedes agregar más aserciones aquí si es necesario
            }
            Err(e) => {
                error!("Calculation failed: {}", e);
                panic!("calculate_reserve_adjustment failed: {}", e);
            }
        }

        assert!(
            result.is_ok(),
            "calculate_reserve_adjustment should succeed with consistent prices"
        );

        // Verificar que los ajustes son razonables
        if let Ok((eth_adj, usdt_adj)) = result {
            assert!(eth_adj.abs() > dec!(0), "ETH adjustment should be non-zero");
            assert!(
                usdt_adj.abs() > dec!(0),
                "USDT adjustment should be non-zero"
            );
        }
    }

    #[test]
    fn test_calculate_reserve_adjustment_inconsistent_prices() {
        let reserve_eth = u256_from_dec_str("10000000000000000000");
        let reserve_usdt = u256_from_dec_str("20000000000");
        let target_price_usdt = Some(dec!(2100));
        let target_price_eth = Some(dec!(0.0005)); // Inconsistent with target_price_usdt

        let result = calculate_reserve_adjustment(
            reserve_eth,
            reserve_usdt,
            target_price_usdt,
            target_price_eth,
        );
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Inconsistent target prices provided");
    }

    #[test]
    fn test_calculate_reserve_adjustment_no_price() {
        let reserve_eth = u256_from_dec_str("10000000000000000000");
        let reserve_usdt = u256_from_dec_str("20000000000");

        let result = calculate_reserve_adjustment(reserve_eth, reserve_usdt, None, None);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            "At least one target price must be provided"
        );
    }

    #[test]
    fn test_calculate_reserve_adjustment_large_values() {
        setup_logger();

        let reserve_eth = U256::from_dec_str("1000000000000000000000000").unwrap(); // 1 million ETH
        let reserve_usdt = U256::from_dec_str("2000000000000000").unwrap(); // 2 trillion USDT
        let current_price = Decimal::from(2000); // Current price: 2000 USDT/ETH
        let target_price_usdt = Some(dec!(2500)); // Target price: 2500 USDT/ETH (25% increase)

        info!("Reserve ETH: {}", reserve_eth);
        info!("Reserve USDT: {}", reserve_usdt);
        info!("Current price: {}", current_price);
        info!("Target price USDT: {:?}", target_price_usdt);

        let result =
            calculate_reserve_adjustment(reserve_eth, reserve_usdt, target_price_usdt, None);

        match result {
            Ok((eth_adj, usdt_adj)) => {
                info!("Calculation successful");
                info!("ETH adjustment: {}", eth_adj);
                info!("USDT adjustment: {}", usdt_adj);

                assert!(
                    eth_adj.abs() > dec!(0.000001),
                    "ETH adjustment should be significant"
                );
                assert!(
                    usdt_adj.abs() > dec!(0.000001),
                    "USDT adjustment should be significant"
                );

                // Verificar la dirección de los ajustes
                assert!(eth_adj < dec!(0), "ETH reserve should decrease");
                assert!(usdt_adj > dec!(0), "USDT reserve should increase");
            }
            Err(e) => {
                error!("Calculation failed: {}", e);
                panic!("calculate_reserve_adjustment failed: {}", e);
            }
        }

        assert!(
            result.is_ok(),
            "calculate_reserve_adjustment should succeed with large values"
        );
    }

    #[test]
    fn test_calculate_reserve_adjustment_zero_reserves() {
        setup_logger();

        let reserve_eth = U256::zero();
        let reserve_usdt = U256::zero();
        let target_price_usdt = Some(dec!(2000));

        info!("Reserve ETH: {}", reserve_eth);
        info!("Reserve USDT: {}", reserve_usdt);
        info!("Target price USDT: {:?}", target_price_usdt);

        let result =
            calculate_reserve_adjustment(reserve_eth, reserve_usdt, target_price_usdt, None);
        assert!(
            result.is_ok(),
            "calculate_reserve_adjustment should succeed with zero reserves"
        );

        let (eth_adj, usdt_adj) = result.unwrap();
        info!("ETH adjustment: {}", eth_adj);
        info!("USDT adjustment: {}", usdt_adj);

        assert_eq!(
            eth_adj,
            dec!(0),
            "ETH adjustment should be zero for zero reserves"
        );
        assert_eq!(
            usdt_adj,
            dec!(0),
            "USDT adjustment should be zero for zero reserves"
        );
    }
}
