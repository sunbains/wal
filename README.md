# Write Ahead Log implementation

[![Rust](https://img.shields.io/badge/Rust-1.65%2B-blue)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](LICENSE)
[![Build](https://github.com/sunbains/wal/actions/workflows/rust.yml/badge.svg)](https://github.com/sunbains/wal/actions)

A high-performance, **multi-writer log** with **async persistence support**.  
It allows **multiple writers** to concurrently write to the buffer.

## Features

- ✅ Multi-writer support
- ✅ Two-phase write (reservation & copy)  
- ✅ Atomic operations for thread-safe access  
- ✅ Asynchronous buffer flushing (without a dedicated thread)  
- ✅ Handles writes larger than the buffer size by persisting them directly  
- ✅ Early segment activation for concurrent writes during rotation

## Installation

To use this library in your Rust project, add the following to your `Cargo.toml`:

```toml
[dependencies]
wal = { git = "https://github.com/sunbains/wal" }
```

# Write-Ahead Log TLA+ Specification

This repository contains a TLA+ specification for a Write-Ahead Log (WAL) system, modeling concurrent write operations and segment rotation. The specification formally verifies the correctness of key WAL behaviors and safety properties.

## Specification Overview

The TLA+ specification models the concurrent write operations and segment rotation in the WAL system, with particular focus on efficient segment rotation and concurrent access. It captures the following key aspects:

### 1. State Space
- Multiple log segments with states (Queued, Active, Writing)
- Multiple concurrent writers
- Segment write positions and LSNs
- Writer counts per segment
- Atomic rotation flag for coordinating segment transitions

### 2. Actions
- `TryReserve`: Writers attempt to reserve space in the active segment
- `Rotate`: Atomic rotation with early activation of next segment
- `Write`: Actual write operation to a segment
- `Complete`: Completion of a write operation
- `CompleteRotation`: Asynchronous completion of segment rotation

### 3. Safety Properties
- `OnlyOneActive`: Only one segment can be active at a time
- `ValidWriterCounts`: Writer counts are always non-negative
- `ValidWritePositions`: Write positions never exceed segment size
- `MonotonicLSNs`: LSNs increase monotonically based on segment order
- `ValidLSNProgression`: Each segment's LSN is based on its predecessor's final LSN

### 4. Liveness Properties
- `WriteCompletion`: Every write operation eventually completes

## Key Behaviors Modeled

### 1. Concurrent Writes
- Multiple writers can attempt to write simultaneously
- Writer count tracking ensures proper synchronization
- Space reservation is atomic
- Writers can proceed to new segment while old one is being persisted

### 2. Segment Rotation
- Atomic rotation lock prevents multiple concurrent rotations
- Early activation of next segment allows immediate writes
- Segments transition through states: Queued → Active → Writing → Queued
- Asynchronous persistence of rotated segments
- LSN progression maintains monotonicity across rotations

### 3. Safety Guarantees
- No data loss during segment rotation
- Proper synchronization between writers
- Monotonic LSN progression within and across segments
- Atomic state transitions prevent race conditions

## Using the Specification

### 1. Model Checking
```bash
tlc WAL.tla
```
This will verify all safety and liveness properties. I used the VS Code TLA+ plugin to test.

### 2. Adjusting Parameters
You can modify the constants in `WAL.cfg` to check different scenarios:
- Increase `NumWriters` to test more concurrent operations
- Increase `NumSegments` to test larger log configurations
- Adjust `SegmentSize` to test different buffer sizes

### 3. Extending the Model
The specification can be extended to model additional features:
- Recovery procedures
- More detailed error conditions
- Additional concurrency patterns

## Implementation Details

The WAL implementation uses atomic operations to ensure thread safety:
1. Atomic segment state and writer count tracking
2. Atomic rotation lock for coordinating segment transitions
3. Early activation of next segment for concurrent writes
4. Lock-free writer coordination
5. Asynchronous segment persistence

## Limitations

### 1. Model Abstractions
The model abstracts away some implementation details:
- Actual data content is not modeled
- Storage operations are simplified
- Error handling is minimal

### 2. State Space Considerations
- Large parameter values may cause state explosion
- Some real-world scenarios may require abstraction
- Complex failure modes are not fully modeled


