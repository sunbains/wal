# Write Ahead Log implementation

[![Rust](https://img.shields.io/badge/Rust-1.65%2B-blue)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](LICENSE)
[![Build](https://github.com/sunbains/log_buffer/actions/workflows/rust.yml/badge.svg)](https://github.com/sunbains/log_buffer/actions)

A high-performance, **multi-writer log ** with **async persistence support**.  
It allows **multiple writers** to concurrently write to the buffer

## Features

- ✅ Multi-writer
- ✅ Two-phase write (reservation & copy)  
- ✅ Atomic operations for thread-safe access  
- ✅ Asynchronous buffer flushing (without a dedicated thread)  
- ✅ Handles writes larger than the buffer size by persisting them directly  

## Installation

To use this library in your Rust project, add the following to your `Cargo.toml`:

```toml
[dependencies]
log_buffer = { git = "https://github.com/sunbains/log_buffer" }
