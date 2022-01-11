uniffi-bindgen scaffolding src/tac_optimizer.udl
uniffi-bindgen generate src/tac_optimizer.udl --language kotlin --no-format
LOCALPATH="../EVMVerifier"
rm "$LOCALPATH/src/main/kotlin/analysis/opt/tac_optimizer.kt" || 0
cp src/uniffi/tac_optimizer/tac_optimizer.kt "$LOCALPATH/src/main/kotlin/analysis/opt/tac_optimizer.kt"

cargo build --release
rm "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.so" || 0
cp "target/release/libtac_optimizer.so" "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.so"




