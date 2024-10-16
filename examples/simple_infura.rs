use tracing::{debug, info};
use uniswapv2_vob::events::uniswap::{decode_event, format_event};
use uniswapv2_vob::utils::logger::setup_logger;
use uniswapv2_vob::web3::infura::{Infura, InfuraConfig};
use web3::types::Log;

async fn process_event(log: Log) {
    if let Some(decoded_event) = decode_event(&log) {
        let formatted_event = format_event(
            &decoded_event,
            log.block_number.map(|n| n.as_u64()),
            log.transaction_hash,
        );
        info!("Decoded event:\n{}", formatted_event);
    } else {
        debug!("Unknown event: {:?}", log);
    }
}

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

    infura
        .get_logs(process_event)
        .await
        .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)?;

    Ok(())
}
