/******************************************************************************
   Author: Joaquín Béjar García
   Email: jb@taunais.com
   Date: 10/10/24
******************************************************************************/

use crate::constants::{BLOCK_OFFSET, BLOCK_RANGE, ETH_USDT_PAIR_ADDRESS, INFURA_URL, SWAP_EVENT_SIGNATURE};
use std::env;
use std::future::Future;
use std::str::FromStr;
use tracing::{debug, error, info};
use web3::transports::WebSocket;
use web3::types::{Address, BlockNumber, FilterBuilder, Log, H256, U64};
use web3::Web3;


pub struct InfuraConfig {
    pub url: String,
    pub api_key: String,
}

impl Default for InfuraConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl InfuraConfig {
    pub fn new() -> Self {
        let api_key = env::var("INFURA_API_KEY").expect("INFURA_API_KEY must be set");
        InfuraConfig::new_with_env(api_key)
    }

    fn new_with_env(api_key: String) -> Self {
        let url = format!("{}{}", INFURA_URL, api_key);
        Self { url, api_key }
    }
}

pub struct Infura {
    pub uniswap_pair_address: Address,
    pub event_signature_hash: H256,
    pub web3: Web3<WebSocket>,
    pub last_block_number: BlockNumber,
    pub current_block_number: BlockNumber,
}

impl Infura {
    pub async fn new(config: InfuraConfig) -> Result<Self, web3::Error> {
        let uniswap_pair_address = Address::from_str(ETH_USDT_PAIR_ADDRESS)
            .map_err(|e| web3::Error::InvalidResponse(format!("Invalid address: {}", e)))?;
        let event_signature_hash =
            H256::from_slice(&web3::signing::keccak256(SWAP_EVENT_SIGNATURE.as_bytes()));
        let transport = WebSocket::new(&config.url).await?;
        let web3 = Web3::new(transport);
        let current_block_number = web3.eth().block_number().await?;
        let last_block_number =
            BlockNumber::Number(current_block_number.saturating_sub(U64::from(BLOCK_OFFSET)));
        let current_block_number = BlockNumber::Number(current_block_number);

        info!(
            "Connected to Infura. Latest block: {:?} current block: {:?}",
            last_block_number, current_block_number
        );
        info!(
            "Infura initialized. Pair address: {}, Event signature: {}",
            ETH_USDT_PAIR_ADDRESS, SWAP_EVENT_SIGNATURE
        );

        Ok(Self {
            uniswap_pair_address,
            event_signature_hash,
            web3,
            last_block_number,
            current_block_number,
        })
    }

    pub fn next_block(&mut self) {
        if let BlockNumber::Number(n) = self.current_block_number {
            self.last_block_number = self.current_block_number;
            self.current_block_number = BlockNumber::Number(n + U64::from(BLOCK_RANGE));
            debug!(
                "Searching for events from block {:?} to {:?}",
                self.last_block_number, self.current_block_number
            );
        } else {
            error!("Expected BlockNumber::Number variant");
            panic!("Expected BlockNumber::Number variant");
        }
    }

    pub async fn get_logs<F, Fut>(&mut self, process_event: F) -> Result<(), web3::Error>
    where
        F: Fn(Log) -> Fut,
        Fut: Future<Output = ()>,
    {
        loop {
            let filter = self.create_filter();
            match self.web3.eth().logs(filter.clone()).await {
                Ok(logs) => {
                    debug!(
                        "Blocks searched: from {:?} to {:?}",
                        self.last_block_number, self.current_block_number
                    );
                    info!("Events found: {}", logs.len());

                    if logs.is_empty() {
                        // If no events found, try to get the latest block number
                        match self.web3.eth().block_number().await {
                            Ok(latest_block) => {
                                debug!("Current latest block: {:?}", latest_block);
                                if let BlockNumber::Number(current) = self.current_block_number {
                                    if latest_block < current {
                                        self.current_block_number =
                                            BlockNumber::Number(latest_block);
                                        self.last_block_number = BlockNumber::Number(
                                            latest_block.saturating_sub(U64::from(1000)),
                                        );
                                    }
                                }
                            }
                            Err(e) => error!("Failed to get latest block number: {:?}", e),
                        }
                    } else {
                        for log in logs {
                            process_event(log).await;
                        }
                    }
                }
                Err(e) => {
                    error!("Error fetching logs: {:?}", e);
                    // Implement a backoff strategy here if needed
                    tokio::time::sleep(tokio::time::Duration::from_secs(30)).await;
                }
            }
            self.next_block();
            tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
        }
    }

    fn create_filter(&self) -> web3::types::Filter {
        let filter = FilterBuilder::default()
            .from_block(self.last_block_number)
            .to_block(self.current_block_number)
            .address(vec![self.uniswap_pair_address])
            .build(); // Removed topic filter temporarily
        debug!("Filter created: {:?}", filter);
        filter
    }
}
