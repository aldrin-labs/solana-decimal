# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a
Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.10.4] 2022-12-16

- `Decimal` has `TryFrom<f64>` functionality.

## [0.10.3] - 2022-12-10

- `Decimal` now derives borsh and serde `Deserialization` and `Serialization` traits.

## [0.10.2] - 2022-12-10

- `Decimal` now has `TryRound<u128>` functionality.
## [0.10.1] - 2022-09-06

### Added

- `f64` can now be rounded, floored and ceiled to `u128`.

## [0.10.0] - 2022-09-03

### Added

- New default error implementation uses `anyhow` which enables us to use this
  crate in context of other blockchains, not only solana.

### Changed

- Anchor's error implementation is no longer default feature but must be enabled
  with feature flag `anchor` and by turning off default features.

## [0.9.0] - 2022-09-03

### Added

- Implementation of the exported math traits for `f64` scalar type.

## [0.8.0] - 2022-09-03

### Removed

- `LargeDecimal` which was a u320 decimal type. This level of precision was not
  necessary and is computationally costly. Use u192 instead.
