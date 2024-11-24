use crate::events::uniswap::{format_event, UniswapEvent};
use crate::orderbook::model::DualSideBook;
use std::sync::Arc;
use tokio::sync::Mutex;
use tracing::info;

/// `EventProcessor` is responsible for processing events in the context of the Uniswap protocol.
/// It maintains an internal state via a Virtual Order Book (`DualSideBook`) that gets updated
/// based on incoming events.
///
/// # Attributes
///
/// * `vob` - An `Arc<Mutex<DualSideBook>>` that represents the Virtual Order Book. The mutex ensures
///           safe concurrent access, while the `Arc` allows shared ownership across threads.
///
///
/// # Methods
///
/// * `new` - Creates a new `EventProcessor` with an initialized `DualSideBook`.
/// * `process_event` - Handles the given `UniswapEvent`, updating the internal state and logging
///                     relevant information. This method is asynchronous and takes optional
///                     block number and transaction hash details.
#[derive(Debug, Clone)]
pub struct EventProcessor {
    vob: Arc<Mutex<DualSideBook>>,
}

impl Default for EventProcessor {
    /// Creates a new `EventProcessor` by invoking the `new` method.
    fn default() -> Self {
        Self::new()
    }
}

impl EventProcessor {
    /// Constructs a new `EventProcessor` instance with an initialized `DualSideBook`.
    ///
    /// # Returns
    ///
    /// * A new instance of `EventProcessor`.
    pub fn new() -> Self {
        EventProcessor {
            vob: Arc::new(Mutex::new(DualSideBook::new())),
        }
    }

    /// Processes a given `UniswapEvent`, updating the internal `DualSideBook` and logging event details.
    ///
    /// # Arguments
    ///
    /// * `event` - The `UniswapEvent` to process.
    /// * `block_number` - An optional `u64` representing the block number.
    /// * `tx_hash` - An optional `web3::types::H256` representing the transaction hash.
    ///
    pub async fn process_event(
        &self,
        event: UniswapEvent,
        block_number: Option<u64>,
        tx_hash: Option<web3::types::H256>,
    ) {
        let mut vob = self.vob.lock().await;
        match event {
            UniswapEvent::Sync {
                reserve_eth,
                reserve_usdt,
            } => {
                info!("Sync event processed, Reserves ETH: {} USDT: {}. Updated Virtual Order Book:\n{}", reserve_eth, reserve_usdt, vob);
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
            } => {

                vob.update_from_swap(eth_in, usdt_in, eth_out, usdt_out, effective_price, side);
                info!(
                    "Swap event processed from: {} to: {}. Updated Virtual Order Book:\n{}",
                    sender, to, vob
                );
            }
        }
        info!(
            "Event details: {}",
            format_event(&event, block_number, tx_hash)
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::uniswap::{Side, UniswapEvent};
    use rust_decimal::Decimal;
    use web3::types::{H160, H256, U256};

    #[tokio::test]
    async fn test_event_processor_new() {
        let processor = EventProcessor::new();
        assert!(Arc::strong_count(&processor.vob) == 1);
    }

    #[tokio::test]
    async fn test_event_processor_default() {
        let processor = EventProcessor::default();
        assert!(Arc::strong_count(&processor.vob) == 1);
    }

    #[tokio::test]
    async fn test_process_sync_event() {
        let processor = EventProcessor::new();
        let event = UniswapEvent::Sync {
            reserve_eth: U256::from(1000),
            reserve_usdt: U256::from(2000000), // Assuming 6 decimals for USDT
        };

        processor
            .process_event(event, Some(12345), Some(H256::zero()))
            .await;

        // Since we can't easily check the internal state of vob, we'll just ensure
        // that the method doesn't panic
    }

    #[tokio::test]
    async fn test_process_swap_event() {
        let processor = EventProcessor::new();
        let event = UniswapEvent::Swap {
            sender: H160::zero(),
            eth_in: U256::zero(),
            usdt_in: U256::from(1000000),                // 1 USDT
            eth_out: U256::from(500000000000000000u128), // 0.5 ETH
            usdt_out: U256::zero(),
            to: H160::zero(),
            effective_price: Decimal::new(2000, 0), // 2000 USDT/ETH
            side: Side::Buy,
        };

        processor
            .process_event(event, Some(12345), Some(H256::zero()))
            .await;

        // Again, we're mainly checking that the method doesn't panic
    }

    #[tokio::test]
    async fn test_multiple_events() {
        let processor = EventProcessor::new();

        // Process a Sync event
        let sync_event = UniswapEvent::Sync {
            reserve_eth: U256::from(1000),
            reserve_usdt: U256::from(2000000),
        };
        processor
            .process_event(sync_event, Some(12345), Some(H256::zero()))
            .await;

        // Process a Swap event
        let swap_event = UniswapEvent::Swap {
            sender: H160::zero(),
            eth_in: U256::zero(),
            usdt_in: U256::from(1000000),
            eth_out: U256::from(500000000000000000u128),
            usdt_out: U256::zero(),
            to: H160::zero(),
            effective_price: Decimal::new(2000, 0),
            side: Side::Buy,
        };
        processor
            .process_event(swap_event, Some(12346), Some(H256::zero()))
            .await;

        // We're mainly ensuring that multiple events can be processed without panicking
    }
}
