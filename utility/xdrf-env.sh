#!/bin/bash

# Run by:
#   cd <xDRF-prefix>
#   source <path to this script>/xdrf-env.sh

# After running following variable will be set
#   LLVM_3_7_0_BIN="<llvm-prefix>/llvm-install/bin"
#   LLVM_3_7_0_LIB="<llvm-prefix>/llvm-install/lib"
#   PATH="$LLVM_3_7_0_BIN:$PATH"
# The settings will only persist in the shell it is run
# and only for the lifetime of the shell.

if [[ -d "$(pwd)/xDRF-build" && \
      -d "$(pwd)/xDRF-src/utility" ]] ; then
    echo "Setting variables:"
    echo "XDRF_BUILD=\"$(pwd)/xDRF-build"
    export XDRF_BUILD="$(pwd)/xDRF-build"
    echo "XDRF_UTILS=\"$(pwd)/xDRF-src/utility"
    export XDRF_UTILS="$(pwd)/xDRF-src/utility"
else

    echo "Could not find some files, check your current working directory."

fi
