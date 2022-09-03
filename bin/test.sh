#!/bin/bash

set -e

# test with default error
cargo test

# test for anchor error
cargo test --no-default-features --features anchor
