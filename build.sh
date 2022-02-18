#!/bin/bash

cd fried-egg && cargo build --release && cd ../../..

rm "$CERTORA/tac_optimizer" 2>/dev/null || true
mv "fried-egg/target/release/tac_optimizer" "$CERTORA"

