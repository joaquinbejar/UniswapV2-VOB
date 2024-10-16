use std::sync::Arc;
use tracing::info;
use uniswapv2_vob::events::uniswap::decode_event;
use uniswapv2_vob::orderbook::event_processor::EventProcessor;
use uniswapv2_vob::utils::logger::setup_logger;
use uniswapv2_vob::web3::infura::{Infura, InfuraConfig};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    setup_logger();

    let config = InfuraConfig::new();
    let mut infura = Infura::new(config)
        .await
        .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)?;

    info!("Connected to Infura. Monitoring Uniswap events...");
    info!("Uniswap pair address: {:?}", infura.uniswap_pair_address);
    info!("Event signature hash: {:?}", infura.event_signature_hash);

    let event_processor = Arc::new(EventProcessor::new());

    infura
        .get_logs(|log| {
            let event_processor = event_processor.clone();
            async move {
                if let Some(decoded_event) = decode_event(&log) {
                    event_processor
                        .process_event(
                            decoded_event,
                            log.block_number.map(|n| n.as_u64()),
                            log.transaction_hash,
                        )
                        .await;
                } else {
                    info!("Unknown event: {:?}", log);
                }
            }
        })
        .await
        .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)?;

    Ok(())
}
