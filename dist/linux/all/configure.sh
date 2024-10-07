#!/bin/bash
set -e
SELFDIR="$( realpath "$( dirname "${BASH_SOURCE[0]}" )" )"
LLC="$(realpath "$(which llc-18)")"
LLVM_DIR="${LLC%/bin/llc}"
echo "Using LLVM installation in $LLVM_DIR"
LLVM_DIR_FOR_SED=$(echo "$LLVM_DIR" | sed 's/\//\\\//g')

sed --regexp-extended --in-place 's/llvm-installation-directory: \~/llvm-installation-directory: "'$LLVM_DIR_FOR_SED'"/' "$SELFDIR/toolchain-config.yml"
