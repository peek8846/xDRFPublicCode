#!/bin/bash

# Run by:
#   cd <pin-prefix>
#   source <path to this script>/pin-env.sh

# After running following variable will be set
#   PIN_BIN="<pin-prefix>/"
# and only for the lifetime of the shell.

echo "Setting variables:"
echo "PIN_BIN=\"$(pwd)/\""
export PIN_BIN="$(pwd)/"


