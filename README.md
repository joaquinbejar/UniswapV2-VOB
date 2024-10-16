# Virtual Order Book for Uniswap V2

[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/uniswapv2-vob.svg)](https://crates.io/crates/uniswapv2-vob)
[![Downloads](https://img.shields.io/crates/d/uniswapv2-vob.svg)](https://crates.io/crates/uniswapv2-vob)
[![Stars](https://img.shields.io/github/stars/joaquinbejar/UniswapV2-VOB.svg)](https://github.com/joaquinbejar/UniswapV2-VOB/stargazers)

[![Build Status](https://img.shields.io/github/workflow/status/joaquinbejar/UniswapV2-VOB/CI)](https://github.com/joaquinbejar/UniswapV2-VOB/actions)
[![Coverage](https://img.shields.io/codecov/c/github/joaquinbejar/UniswapV2-VOB)](https://codecov.io/gh/joaquinbejar/UniswapV2-VOB)
[![Dependencies](https://img.shields.io/librariesio/github/joaquinbejar/UniswapV2-VOB)](https://libraries.io/github/joaquinbejar/UniswapV2-VOB)

## Table of Contents

<table style="width: 100%; border-collapse: collapse;">
<tr style="border: none;">
<td width="50%" valign="top" style="border: none; padding: 10px;">

1. [Introduction](#introduction)
2. [Features](#features)
3. [Project Structure](#project-structure)
4. [Setup Instructions](#setup-instructions)
5. [Library Usage](#library-usage)
6. [Usage Examples](#usage-examples)
7. [Testing](#testing)
8. [Contribution and Contact](#contribution-and-contact)

</td>
<td width="50%" align="center" style="border: none; padding: 10px;">

<img src="doc/images/logo.png" alt="Virtual Order Book for Uniswap V2" style="width: 300px; height: 300px; max-width: 100%;">

</td>
</tr>
</table>



## Introduction

UniswapV2-VOB is an advanced on-chain liquidity intelligence platform that creates a virtual order book for Uniswap V2's ETH/USDT pair. This Rust-based project integrates with the Ethereum blockchain via Infura, processes Uniswap events in real-time, and constructs a simulated order book. It offers insights into liquidity depth, effective pricing, and swap dynamics, making it a valuable tool for traders, researchers, and DeFi enthusiasts. Features include real-time event processing, price impact analysis, and a virtual order book visualization.

## Features

1. **Real-time Blockchain Data Fetching**: Utilizes Web3 in Rust to connect directly with Ethereum nodes via Infura and fetch live blockchain data.
2. **Virtual Order Book Construction**: Builds and maintains a virtual order book for the Uniswap V2 ETH/USDT pair based on real-time liquidity changes.
3. **Dual-sided Order Book**: Maintains separate order books for ETH/USDT and USDT/ETH swaps, providing a comprehensive view of the market.
4. **Effective Price Calculation**: Calculates and tracks the effective price for each swap, offering insights into actual trading conditions.
5. **Event Streaming and Processing**: Efficiently processes Uniswap Swap and Sync events in real-time, updating the virtual order book accordingly.
6. **Liquidity Depth Analysis**: Provides instant insights into liquidity depth and simulates price impact for various trading sizes.
7. **Efficient Data Processing**: Leverages Rust's performance to handle large streams of blockchain events efficiently.
8. **Configurable Logging**: Offers flexible logging options with different verbosity levels for debugging and monitoring.
9. **Decimal Precision**: Utilizes high-precision decimal calculations to ensure accuracy in financial computations.
10. **Reserve Tracking**: Keeps track of ETH and USDT reserves, providing a clear picture of the pool's liquidity state.

## Project Structure

The project is structured as follows:

1. **Constants** (`constants.rs`): Defines important constants used throughout the project, such as contract addresses and decimal precisions.

2. **Event Processing** (`events/`):
    - `uniswap.rs`: Handles decoding and processing of Uniswap events (Sync and Swap).

3. **Order Book** (`orderbook/`):
    - `model.rs`: Implements the `VirtualOrderBook` and `DualSideBook` structures.
    - `logic.rs`: Contains logic for updating reserves and calculating order book entries.

4. **Infura Integration** (`infura.rs`): Manages the connection to Infura for fetching blockchain data.

5. **Event Processor** (`event_processor.rs`): Coordinates the processing of events and updating of the virtual order book.

6. **Utils** (`utils/`):
    - `logic.rs`: Provides utility functions for mathematical operations and conversions.
    - `logger.rs`: Implements a configurable logging system.

7. **Main Application** (`main.rs`): Entry point of the application, setting up the event loop and Infura connection.

This structure reflects the modular design of the UniswapV2-VOB project, separating concerns into distinct components for event processing, order book management, blockchain interaction, and utility functions.

## Library Usage

TODO!

## Usage Examples

TODO!

## Setup Instructions

1. Clone the repository:
```shell
git clone https://github.com/joaquinbejar/UniswapV2-VOB.git
cd UniswapV2-VOB
```

2. Install dependencies:
```shell
make build
```

3. Set up environment variables:
   Create a `.env` file in the project root and add the following:
```
INFURA_API_KEY=your_infura_api_key
LOGLEVEL=INFO  # Options: ERROR, WARN, INFO, DEBUG, TRACE
```

4. Run the platform:
```shell
make run
```

## Usage

The UniswapV2-VOB project is designed to run as a standalone application that processes Uniswap V2 events and maintains a virtual order book. Here's a basic overview of its operation:

1. The application connects to the Ethereum network via Infura.
2. It listens for Swap and Sync events from the Uniswap V2 ETH/USDT pair contract.
3. As events are received, it updates the virtual order book, calculating effective prices and liquidity depths.
4. The current state of the order book is logged to the console.

## Configuration

You can adjust the following in `constants.rs`:
- `ETH_USDT_PAIR_ADDRESS`: The address of the Uniswap V2 ETH/USDT pair contract.
- `VOB_DEPTH`: The depth of the virtual order book (number of price levels).

## Logging

Adjust the `LOGLEVEL` environment variable to control the verbosity of logging:
- `ERROR`: Only log errors.
- `WARN`: Log warnings and errors.
- `INFO`: Log general information, warnings, and errors.
- `DEBUG`: Log detailed debugging information.
- `TRACE`: Log very detailed tracing information.

## Testing

To run the test suite:

```shell
make test
```

## Contribution and Contact

We welcome contributions to this project! If you would like to contribute, please follow these steps:

1. Fork the repository on GitLab.
2. Create a new branch for your feature or bug fix.
3. Make your changes and ensure that the project still builds and all tests pass.
4. Commit your changes and push your branch to your forked repository.
5. Submit a merge request to the main repository.

If you have any questions, issues, or would like to provide feedback, please feel free to contact the project maintainer:

**[Joaquín Béjar García]**
- Email: [jb@taunais.com]
- GitLab: [joaquinbejar]

We appreciate your interest and look forward to your contributions!
