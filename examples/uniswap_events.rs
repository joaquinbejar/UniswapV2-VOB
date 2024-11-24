use std::env;
use std::str::FromStr;
use std::time::Duration;
use tokio::time::sleep;
use web3::types::{Address, BlockNumber, FilterBuilder, Log, H256, U256};
use web3::{transports::WebSocket, Web3};

fn format_token_amount(amount: U256, decimals: u32) -> String {
    let mut value = amount.to_string();
    if value.len() <= decimals as usize {
        value = "0".repeat(decimals as usize - value.len() + 1) + &value;
    }
    let decimal_index = value.len() - decimals as usize;
    format!("{}.{}", &value[..decimal_index], &value[decimal_index..])
}

fn create_filter(
    pair: Address,
    event_hash: H256,
    from_block: BlockNumber,
    to_block: BlockNumber,
) -> web3::types::Filter {
    FilterBuilder::default()
        .from_block(from_block)
        .to_block(to_block)
        .address(vec![pair])
        .topics(Some(vec![event_hash]), None, None, None)
        .build()
}

async fn process_event(event: Log, amm_name: &str) {
    println!("New Swap event in {}:", amm_name);
    println!("  Block: {:?}", event.block_number.unwrap());
    println!(
        "  Transaction: 0x{}",
        hex::encode(event.transaction_hash.unwrap().0)
    );

    if let Some(data) = event.data.0.get(..128) {
        let amount0_in = U256::from_big_endian(&data[0..32]);
        let amount1_in = U256::from_big_endian(&data[32..64]);
        let amount0_out = U256::from_big_endian(&data[64..96]);
        let amount1_out = U256::from_big_endian(&data[96..128]);

        println!("  ETH In:   {} ETH", format_token_amount(amount0_in, 18));
        println!("  USDT In:  {} USDT", format_token_amount(amount1_in, 6));
        println!("  ETH Out:  {} ETH", format_token_amount(amount0_out, 18));
        println!("  USDT Out: {} USDT", format_token_amount(amount1_out, 6));
    } else {
        println!("  Unable to decode event data");
    }

    if let Some(to) = event.topics.get(2) {
        println!("  To: 0x{}", hex::encode(&to.0[12..]));
    }

    println!();
}

#[tokio::main]
async fn main() -> web3::Result<()> {
    // let infura_api_key = env::var("INFURA_API_KEY").expect("INFURA_API_KEY must be set");
    // let infura_url = format!("wss://mainnet.infura.io/ws/v3/{}", infura_api_key);
    // let websocket = WebSocket::new(&infura_url).await?;

    let ws_url = env::var("WS_URL").expect("WS_URL must be set");
    let websocket = WebSocket::new(&ws_url).await?;

    let web3 = Web3::new(websocket);

    let block_number = web3.eth().block_number().await?;
    println!("Connected to Infura. Latest block: {}", block_number);

    // Specific pair contracts (ETH/USDT pairs)
    let uniswap_pair = Address::from_str("0x0d4a11d5EEaaC28EC3F61d100daF4d40471f1852").unwrap();
    let sushiswap_pair = Address::from_str("0x06da0fd433C1A5d7a4faa01111c044910A184553").unwrap();

    // Swap event signature
    let swap_event_signature = "Swap(address,uint256,uint256,uint256,uint256,address)";
    let event_signature_hash =
        H256::from_slice(&web3::signing::keccak256(swap_event_signature.as_bytes()));
    println!("Event signature hash: {:?}", event_signature_hash);

    // Start 10 blocks in the past
    let mut last_block = block_number.saturating_sub(web3::types::U64::from(100));

    loop {
        let current_block = web3.eth().block_number().await?;
        println!(
            "Searching for events from block {:?} to {:?}",
            last_block, current_block
        );

        let uniswap_filter = create_filter(
            uniswap_pair,
            event_signature_hash,
            BlockNumber::Number(last_block),
            BlockNumber::Number(current_block),
        );
        let sushiswap_filter = create_filter(
            sushiswap_pair,
            event_signature_hash,
            BlockNumber::Number(last_block),
            BlockNumber::Number(current_block),
        );

        // Get new Uniswap events
        match web3.eth().logs(uniswap_filter).await {
            Ok(logs) => {
                println!("Uniswap events found: {}", logs.len());
                for log in logs {
                    process_event(log, "Uniswap").await;
                }
            }
            Err(e) => println!("Error fetching Uniswap logs: {:?}", e),
        }

        // Get new SushiSwap events
        match web3.eth().logs(sushiswap_filter).await {
            Ok(logs) => {
                println!("SushiSwap events found: {}", logs.len());
                for log in logs {
                    process_event(log, "SushiSwap").await;
                }
            }
            Err(e) => println!("Error fetching SushiSwap logs: {:?}", e),
        }

        last_block = current_block + web3::types::U64::from(1);

        println!("Waiting 10 seconds before next search...");
        sleep(Duration::from_secs(10)).await;
    }
}
