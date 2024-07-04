#!/bin/bash

set -euxo
source /root/.cargo/env

cd /root/rox
cargo build --release --features dbg-stress-gc

cd /root/craftinginterpreters
dart tool/bin/test.dart clox --interpreter /root/rox/target/release/rox
