# Dentrado: Functional-Reactive Database Management System

[![CI](https://github.com/luna-spirito/dentrado-poc/actions/workflows/ci.yml/badge.svg)](https://github.com/luna-spirito/dentrado-poc/actions/workflows/ci.yml)

A proof-of-concept in-memory implementation of a **functional-reactive database management system** written in Haskell. Final implementation is currently being developed in Rust.

Please look into [en.pdf](./en.pdf) (or original version [ru.pdf](./ru.pdf) in Russian) for the full report, this README contains a brief summary.

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
- `StateGraph` abstraction to cache dependency graph to support efficient retroactive updates.

To verify the resulting implementation, a simple RBAC system is modeled, with privileged users being able to change access level of other users ([tests/Model.hs](./tests/Model.hs), [tests/Shared/Model.hs](tests/Shared/Model.hs))

```hs
-- | Model: Event: enum that defines list of events that are being processed to construct a site.
data Event
  = CreateUser -- #0: Marker. Is sent when a new user is created.
  | AdminSetAccessLevel !(W1 Maybe UserId) !UserId !(W SiteAccessLevel)
  -- ^ #1: Is sent when some admin (or superuser, denoted by Nothing) assignes new SiteAccessLevel to the user.
  deriving (Show, Generic)

{- | The Gear that processes the test input, returning the StateGraph
which associates SiteAccessLevel to each UserId throughout all points of time.
-}
status ∷ GearTemplate' () (SG.StateGraph UserId (W SiteAccessLevel))
status =
  $sFreshI
    $ builtinAsmGearTemplate
    $ SG.mkStateGraph
      (asmGear events)
      ( SG.StateGraphDepsNil
      , unW >>> \case -- BEGINNING OF EVENT PROCESSING BODY
          AdminSetAccessLevel (W1 adminM) target level → do
            hasAccess ← case adminM of
              Nothing → pure True
              Just admin →
                SG.query admin <&> \case
                  Just (W SalAdmin) → True
                  _ → False
            when hasAccess $ SG.update target $ pure level
          _ → pure ()
      )
```

QuickCheck test is being used to demonstrate that, no matter in which order event log is being merged, the system converges to a single final state, performing automatic history rewrites when necessary.

# Known limitations

* This proof-of-concept is completely in-memory, and while research some research into on-disk serialization was done, no proper integration with on-disk storage system was made.
* Essential property of cache irrelevance (that `Gear`s act as pure functions) was formalized, but wasn't formally verified for implemented `Gear`s.
* No network communication implemented.

# Future work

* Making a feature-complete DBMS implementation with data storage and networking.
* Integrating [Fadeno language](https://github.com/luna-spirito/fadeno-lang) as a scripting language to describe `Gear`s.
