#!/bin/bash

if [[ $# < 2 ]] ; then
    echo "Requires at least two argument, the input .s file and the output .s file."
    exit 1
fi

inputFile="$1"
outputFile="$2"

sed 's/^\t.ascii\t"\(begin\|end\)_resndrf \([0-9]\+\)"$/\tmovl\t\$\2, %edi\n\tcallq\t\1_NDRF/' "$inputFile" \
> "$outputFile"
