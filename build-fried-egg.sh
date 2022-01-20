cargo install uniffi_bindgen
uniffi-bindgen scaffolding src/tac_optimizer.udl
uniffi-bindgen generate src/tac_optimizer.udl --language kotlin --no-format
LOCALPATH="../EVMVerifier"
rm "$LOCALPATH/src/main/kotlin/analysis/opt/tac_optimizer.kt" || true
cp src/uniffi/tac_optimizer/tac_optimizer.kt "$LOCALPATH/src/main/kotlin/analysis/opt/tac_optimizer.kt"

cargo build --release
rm "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.so" 2>/dev/null || true
rm "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.dylib" 2>/dev/null || true
rm "$LOCALPATH/src/main/resources/uniffi_tac_optimizer.dll" 2>/dev/null || true
cp "target/release/libtac_optimizer.so" "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.so" 2>/dev/null && linux=true || linux=false
cp "target/release/libtac_optimizer.dylib" "$LOCALPATH/src/main/resources/libuniffi_tac_optimizer.dylib" 2>/dev/null && mac=true || mac=false
cp "target/release/tac_optimizer.dll" "$LOCALPATH/src/main/resources/uniffi_tac_optimizer.dll" 2>/dev/null && windows=true || windows=false

if ! $linux && ! $mac && ! $windows; then
    echo "ERROR: No fried-egg binary found!"
    exit 1
fi




