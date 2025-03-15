# Write Ahead Log implementation

[![Rust](https://img.shields.io/badge/Rust-1.65%2B-blue)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](LICENSE)
[![Build](https://github.com/sunbains/log_buffer/actions/workflows/rust.yml/badge.svg)](https://github.com/sunbains/log_buffer/actions)

A high-performance, **multi-writer log** with **async persistence support**.  
It allows **multiple writers** to concurrently write to the buffer.

## Features

- ✅ Multi-writer support
- ✅ Two-phase write (reservation & copy)  
- ✅ Atomic operations for thread-safe access  
- ✅ Asynchronous buffer flushing (without a dedicated thread)  
- ✅ Handles writes larger than the buffer size by persisting them directly  

## Installation

To use this library in your Rust project, add the following to your `Cargo.toml`:

```toml
[dependencies]
log_buffer = { git = "https://github.com/sunbains/log_buffer" }
```

# Write-Ahead Log TLA+ Specification

This repository also contains a TLA+ specification for a Write-Ahead Log (WAL) system, modeling concurrent write operations and segment rotation. The specification formally verifies the correctness of key WAL behaviors and safety properties.

## Specification Overview

This TLA+ specification provides a formal model for verifying the correctness of the WAL implementation, particularly focusing on concurrent operations and segment management. It can be used to catch potential race conditions and ensure the system maintains its safety properties under various conditions.

The TLA+ specification models the concurrent write operations and segment rotation in the WAL system. It captures the following key aspects:

### 1. State Space
- Multiple log segments with states (Queued, Active, Writing)
- Multiple concurrent writers
- Segment write positions and LSNs
- Writer counts per segment

### 2. Actions
- `TryReserve`: Writers attempt to reserve space in the active segment
- `Rotate`: Rotation of segments when the current one is full
- `Write`: Actual write operation to a segment
- `Complete`: Completion of a write operation

### 3. Safety Properties
- `OnlyOneActive`: Only one segment can be active at a time
- `ValidWriterCounts`: Writer counts are always non-negative
- `ValidWritePositions`: Write positions never exceed segment size
- `MonotonicLSNs`: LSNs are monotonically increasing

### 4. Liveness Properties
- `WriteCompletion`: Every write operation eventually completes

## Configuration

The configuration file (`WAL.cfg`) sets up a small model for checking:
- 3 log segments
- Segment size of 4 units
- 2 concurrent writers
- Initial LSN of 0

## Key Behaviors Modeled

### 1. Concurrent Writes
- Multiple writers can attempt to write simultaneously
- Writer count tracking ensures proper synchronization
- Space reservation is atomic

### 2. Segment Rotation
- Segments transition through states: Queued → Active → Writing
- Only one segment is active at any time
- LSNs are updated during rotation
- Write positions are reset after rotation

### 3. Safety Guarantees
- No data loss during segment rotation
- Proper synchronization between writers
- Monotonic LSN progression

## Using the Specification

### 1. Model Checking
```bash
tlc WAL.tla
```
This will verify all safety and liveness properties. I used the VS Code plugin to test.

### 2. Adjusting Parameters
You can modify the constants in `WAL.cfg` to check different scenarios:
- Increase `NumWriters` to test more concurrent operations
- Increase `NumSegments` to test larger log configurations
- Adjust `SegmentSize` to test different buffer sizes

### 3. Extending the Model
The specification can be extended to model additional features:
- Persistence operations
- Recovery procedures
- More detailed error conditions

## Limitations

### 1. Model Abstractions
The model abstracts away some implementation details:
- Actual data content is not modeled
- Storage operations are simplified
- Error handling is minimal

### 2. State Space Considerations
- Large parameter values may cause state explosion
- Some real-world scenarios may require abstraction


