#!/bin/bash

# Run by:
#   cd <llvm-prefix>
#   source <path to this script>/llvm-env.sh

# After running following variable will be set
#   LLVM_3_7_0_BIN="<llvm-prefix>/llvm-install/bin"
#   LLVM_3_7_0_LIB="<llvm-prefix>/llvm-install/lib"
#   PATH="$LLVM_3_7_0_BIN:$PATH"
# The last assignment pre-pends the LLVM bin directory
# to the PATH, meaning it will take precedence
# over any other LLVM install.
# The settings will only persist in the shell it is run
# and only for the lifetime of the shell.

if [[ -x "$(pwd)/llvm-3.8.0.install/bin/clang-3.8" && \
      -x "$(pwd)/llvm-3.8.0.install/bin/opt" && \
      -e "$(pwd)/llvm-3.8.0.install/lib/libclang.so.3.8" ]] ; then

    echo "Setting variables:"
    echo "LLVM_3_8_0_BIN=\"$(pwd)/llvm-3.8.0.install/bin\""
    export LLVM_3_8_0_BIN="$(pwd)/llvm-3.8.0.install/bin"
    echo "LLVM_3_8_0_LIB=\"$(pwd)/llvm-3.8.0.install/lib\""
    export LLVM_3_8_0_LIB="$(pwd)/llvm-3.8.0.install/lib"
    echo "PATH=\"$LLVM_3_8_0_BIN:\$PATH\""
    export PATH="$LLVM_3_8_0_BIN:$PATH"

else

    echo "Could not find some files, check your current working directory."

fi
