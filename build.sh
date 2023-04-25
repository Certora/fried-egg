#!/bin/bash

cd fried-egg && cargo build --release && cd ../

# Assign the first argument to the variable 'dir', or set it to $CERTORA if no argument was passed
dir=${1:-$CERTORA}

rm "$dir/tac_optimizer" 2>/dev/null || true
mv "fried-egg/target/release/tac_optimizer" "$dir"

