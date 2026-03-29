# Dentrado: Functional-Reactive Database Management System

A proof-of-concept in-memory implementation of a **functional-reactive database management system** written in Haskell. Final implementation is currently being developed in Rust.

Please look into [en.pdf](./end.pdf) (or original version [ru.pdf](./ru.pdf) in Russian) for the full report, this README contains a brief summary.

## Runnings tests

```sh
nix develop .#
cabal v2-test
```

## Features

Dentrado proposes a **functional-reactive architecture** for DBMS as an alternative to imperative approaches (PostgreSQL, MySQL, Oracle). It's based on:

- **Append-only event log** as single source of truth.
- **Immutable data structures** for storage.
- **Functional reactive programming** to incrementally produce final state by aggregating the event list.

This foundation enables:
- **Strong eventual consistency** with no need for "master"/"slave" nodes, achievable simply by synchronizing event logs.
- Complex **retroactive updates** and time travel, log audit.
- Dynamic behaviour and flexible schema.
- Non-destructive updates.
- Potential for **formal verification**.
- Support for complex data structures, domain-specific data organization and custom indexes.
- Inherent suitability for version control systems.

## Architecture

- The system is event-sourced, meaning that the event list acts as a sinle point of truth.
- Event entries are ordered lexicographically by `(timestamp, node_id, counter)`, allowing for deterministic merging in a distributed environment
- All other data is derived from the event list via multi-stage processin by reactive cells (called `Gear`s), which act as pure functions, but are implemented as state machines with internal "cache" as a state for computational efficiency.
- Internal "cache" is stored as immutable data structures.

## Implementation details

The prototype is implemented in Haskell and demonstrates:
- Definition of `Gear`, with Haskell lambdas serving as step functions.
- Experiments into representation of on-disk data structures in Haskel; support for lazy data structures as intermediate outputs via `Delay`.
- Definition of applicative functor `Asm` ("Assembly") for easy composition of the outputs of multiple `Gear`s for future processing.
- `StateGraph` abstraction to cache dependency graph to support retroactive updates.
