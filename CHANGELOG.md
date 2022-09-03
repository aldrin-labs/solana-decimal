# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a
Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.8.0] - 20022-09-03

### Removed

- `LargeDecimal` which was a u320 decimal type. This level of precision was not
  necessary and is computationally costly.
