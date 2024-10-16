use num_traits::{FromPrimitive, ToPrimitive, Zero};
use rust_decimal::Decimal;
use std::str::FromStr;
use web3::types::U256;

/// Converts a `U256` integer to a `Decimal` with a specified number of decimal places.
///
/// # Arguments
///
/// * `value` - The `U256` integer value to be converted.
/// * `decimals` - The number of decimal places to ensure in the resulting `Decimal`.
///
/// # Returns
///
/// Returns a `Decimal` representation of the `U256` value with the specified number of decimal places.
///
/// # Panics
///
/// This function will panic if the `U256` value cannot be converted to a `Decimal`
/// or if the string operations on the value fail.
///
/// ```
pub(crate) fn u256_to_decimals(value: U256, decimals: u8) -> Decimal {
    let value_str = value.to_string();
    let len = value_str.len();

    if len > 28 {
        let scale_factor = len - 28;
        let scaled_value = &value_str[0..28];
        let scaled_decimal = Decimal::from_str(scaled_value)
            .unwrap_or_else(|_| panic!("Failed to convert scaled U256 to Decimal"));

        let log_scale = (scale_factor as f64).log10();
        let log_decimals = (decimals as f64).log10();
        let log_adjustment = log_scale - log_decimals;

        if log_adjustment > 0.0 {
            scaled_decimal * Decimal::from_f64(10f64.powf(log_adjustment)).unwrap_or(Decimal::MAX)
        } else {
            scaled_decimal / Decimal::from_f64(10f64.powf(-log_adjustment)).unwrap_or(Decimal::MAX)
        }
    } else {
        let mut value_str = value.to_string();
        if value_str.len() <= decimals as usize {
            value_str.insert_str(0, &"0".repeat(decimals as usize - value_str.len() + 1));
        }
        let decimal_index = value_str.len() - decimals as usize;
        value_str.insert(decimal_index, '.');

        Decimal::from_str(&value_str)
            .unwrap_or_else(|_| panic!("Failed to convert U256 to Decimal"))
    }
}

/// Converts a `Decimal` value to `U256` by scaling it up based on the given
/// number of decimal places. The value is multiplied by 10 raised to the power
/// of `decimals`, truncated to its integer part, and finally converted to `U256`.
///
/// # Arguments
/// * `value` - The `Decimal` value to be converted.
/// * `decimals` - The number of decimal places to scale the value.
///
/// # Returns
/// * `U256` - The converted `U256` value.
///
/// # Panics
/// * Panics if the conversion to `i128` fails.
///
pub(crate) fn decimal_to_u256(value: Decimal, decimals: u8) -> U256 {
    let factor = Decimal::from(10u64.pow(decimals as u32));
    let scaled_value = value * factor;

    // Ensure the scaled value is truncated and converted to integer safely
    let integer_part = scaled_value
        .trunc()
        .to_i128()
        .expect("Failed to convert to i128");

    // Convert the integer part to U256
    U256::from(integer_part.unsigned_abs()) // Ensure it's converted properly to U256
}

/// Solves a system of two linear equations with two unknowns using
/// the determinant method.
///
/// The system of equations is represented as:
/// a1 * x + b1 * y = c1
/// a2 * x + b2 * y = c2
///
/// # Arguments
/// * `a1`, `b1`, `c1` - Coefficients of the first equation.
/// * `a2`, `b2`, `c2` - Coefficients of the second equation.
///
/// # Returns
/// * `Option<(Decimal, Decimal)>` - The solution `(x, y)` as an option. Returns `None` if there is no unique solution.
///
pub(crate) fn solve_linear_system(
    a1: Decimal,
    b1: Decimal,
    c1: Decimal,
    a2: Decimal,
    b2: Decimal,
    c2: Decimal,
) -> Option<(Decimal, Decimal)> {
    let det = a1 * b2 - a2 * b1;

    if det.is_zero() {
        return None;
    }

    let det_x = c1 * b2 - c2 * b1;
    let det_y = a1 * c2 - a2 * c1;

    let x = det_x / det;
    let y = det_y / det;

    Some((x, y))
}

/// Calculates the square root of a `Decimal` value using the Babylonian method
/// (also known as Heron's method).
///
/// # Arguments
/// * `value` - The `Decimal` value to compute the square root of.
///
/// # Returns
/// * `Decimal` - The square root of the input value.
///
/// # Panics
/// * Panics if the input value is negative.
/// * Panics if the input value is too large for the square root calculation.
///
pub(crate) fn decimal_sqrt(value: Decimal) -> Decimal {
    if value < Decimal::zero() {
        panic!("Cannot calculate square root of negative number");
    }
    if value == Decimal::zero() {
        return Decimal::zero();
    }
    if value > Decimal::MAX / Decimal::new(2, 0) {
        panic!("Value too large for square root calculation");
    }

    let mut x = value;
    let mut x_prev;
    let epsilon = Decimal::new(1, 28); // Increased precision

    loop {
        x_prev = x;
        x = (x + value / x) / Decimal::new(2, 0);
        if (x - x_prev).abs() <= epsilon * x {
            break;
        }
    }

    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u256_to_decimals() {
        // Test case 1: Converting 1 ETH (18 decimals)
        let value = U256::from_dec_str("1000000000000000000").unwrap(); // 1 ETH in U256 with 18 decimals
        let result = u256_to_decimals(value, 18);
        assert_eq!(result, Decimal::from_str("1").unwrap());

        // Test case 2: Converting 1000 USDT (6 decimals)
        let value = U256::from_dec_str("1000000000").unwrap(); // 1000 USDT in U256 with 6 decimals
        let result = u256_to_decimals(value, 6);
        assert_eq!(result, Decimal::from_str("1000").unwrap());

        // Test case 3: Converting a large value with 18 decimals
        let value = U256::from_dec_str("123456789000000000000000000").unwrap();
        let result = u256_to_decimals(value, 18);
        assert_eq!(result, Decimal::from_str("123456789").unwrap());
    }

    #[test]
    fn test_decimal_to_u256() {
        // Test case 1: Converting 1 ETH (18 decimals)
        let value = Decimal::from_str("1").unwrap(); // 1 ETH as a Decimal
        let result = decimal_to_u256(value, 18);
        assert_eq!(result, U256::from_dec_str("1000000000000000000").unwrap());

        // Test case 2: Converting 1000 USDT (6 decimals)
        let value = Decimal::from_str("1000").unwrap(); // 1000 USDT as a Decimal
        let result = decimal_to_u256(value, 6);
        assert_eq!(result, U256::from_dec_str("1000000000").unwrap());

        // Test case 3: Converting a large decimal value with 18 decimals
        let value = Decimal::from_str("123456789").unwrap();
        let result = decimal_to_u256(value, 18);
        assert_eq!(
            result,
            U256::from_dec_str("123456789000000000000000000").unwrap()
        );
    }

    #[test]
    fn test_round_trip_conversion() {
        // Test case 1: Round-trip conversion for 1 ETH
        let eth_value = U256::from_dec_str("1000000000000000000").unwrap(); // 1 ETH in U256
        let decimal_value = u256_to_decimals(eth_value, 18);
        let converted_back = decimal_to_u256(decimal_value, 18);
        assert_eq!(eth_value, converted_back);

        // Test case 2: Round-trip conversion for 1000 USDT
        let usdt_value = U256::from_dec_str("1000000000").unwrap(); // 1000 USDT in U256
        let decimal_value = u256_to_decimals(usdt_value, 6);
        let converted_back = decimal_to_u256(decimal_value, 6);
        assert_eq!(usdt_value, converted_back);
    }
}

#[cfg(test)]
mod tests_solve_linear_system {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_unique_solution() {
        // Caso: 3x + 2y = 5 y 4x + 3y = 7
        let a1 = dec!(3);
        let b1 = dec!(2);
        let c1 = dec!(5);
        let a2 = dec!(4);
        let b2 = dec!(3);
        let c2 = dec!(7);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_some());
        let (x, y) = result.unwrap();
        assert_eq!(x, dec!(1));
        assert_eq!(y, dec!(1));
    }

    #[test]
    fn test_inconsistent_system() {
        // Caso inconsistente: 2x + 4y = 6 y 4x + 8y = 10
        let a1 = dec!(2);
        let b1 = dec!(4);
        let c1 = dec!(6);
        let a2 = dec!(4);
        let b2 = dec!(8);
        let c2 = dec!(10);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_none()); // Sistema inconsistente
    }

    #[test]
    fn test_infinite_solutions() {
        // Caso con infinitas soluciones: 2x + 4y = 8 y 4x + 8y = 16
        let a1 = dec!(2);
        let b1 = dec!(4);
        let c1 = dec!(8);
        let a2 = dec!(4);
        let b2 = dec!(8);
        let c2 = dec!(16);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_none()); // Sistema con infinitas soluciones
    }

    #[test]
    fn test_zero_coefficient() {
        // Caso: x + 0y = 3 y 0x + y = 4
        let a1 = dec!(1);
        let b1 = dec!(0);
        let c1 = dec!(3);
        let a2 = dec!(0);
        let b2 = dec!(1);
        let c2 = dec!(4);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_some());
        let (x, y) = result.unwrap();
        assert_eq!(x, dec!(3));
        assert_eq!(y, dec!(4));
    }

    #[test]
    fn test_negative_coefficients() {
        // Caso: -x + y = 1 y -2x + 3y = 2
        let a1 = dec!(-1);
        let b1 = dec!(1);
        let c1 = dec!(1);
        let a2 = dec!(-2);
        let b2 = dec!(3);
        let c2 = dec!(2);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_some());
        let (x, y) = result.unwrap();
        assert_eq!(x, dec!(-1)); // El valor correcto de x es -1
        assert_eq!(y, dec!(0)); // El valor correcto de y es 0
    }

    #[test]
    fn test_two_swaps() {
        let a1 = dec!(4800); // USDT In
        let b1 = dec!(-1.817457120942687720); // ETH Out
        let c1 = dec!(8723.794180524901056);
        let a2 = dec!(9800);
        let b2 = dec!(-3.710363103308561298);
        let c2 = dec!(36361.558413023900720);

        let result = solve_linear_system(a1, b1, c1, a2, b2, c2);
        assert!(result.is_some());
        let (x, y) = result.unwrap();
        assert_eq!(x, dec!(25220.583165923481599812772756));
        assert_eq!(y, dec!(66604088.760820574518660300776));
    }
}

#[cfg(test)]
mod tests_decimal_sqrt {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_sqrt_of_zero() {
        assert_eq!(decimal_sqrt(dec!(0)), dec!(0));
    }

    #[test]
    fn test_sqrt_of_one() {
        assert_eq!(decimal_sqrt(dec!(1)), dec!(1));
    }

    #[test]
    fn test_sqrt_of_four() {
        assert_eq!(decimal_sqrt(dec!(4)), dec!(2));
    }

    #[test]
    fn test_sqrt_of_two() {
        let result = decimal_sqrt(dec!(2));
        assert!((result * result - dec!(2)).abs() < dec!(0.0000000000000001));
    }

    #[test]
    fn test_sqrt_of_large_number() {
        let result = decimal_sqrt(dec!(1000000));
        assert!((result * result - dec!(1000000)).abs() < dec!(0.0000000000000001));
    }

    #[test]
    fn test_sqrt_of_small_number() {
        let result = decimal_sqrt(dec!(0.0001));
        assert!((result * result - dec!(0.0001)).abs() < dec!(0.0000000000000001));
    }

    #[test]
    fn test_sqrt_precision() {
        let result = decimal_sqrt(dec!(2));
        assert_eq!(result.to_string(), "1.4142135623730950488016887242");
    }

    #[test]
    #[should_panic(expected = "Cannot calculate square root of negative number")]
    fn test_sqrt_of_negative_number() {
        decimal_sqrt(dec!(-1));
    }

    #[test]
    #[should_panic(expected = "Value too large for square root calculation")]
    fn test_sqrt_of_max_decimal() {
        let max_decimal = Decimal::MAX;
        decimal_sqrt(max_decimal);
    }
}
