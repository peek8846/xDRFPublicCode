#!/bin/bash

filename="$1"
shift

"$PIN_BIN"/pin -injection child -t "$PIN_BIN"/source/tools/GEMS/obj-intel64/consistency-checker-SPEL.so -o "$filename" -- $@
