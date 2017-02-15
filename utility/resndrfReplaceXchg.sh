#!/bin/bash

if [[ $# < 2 ]] ; then
    echo "Requires at least two argument, the input .s file and the output .s file."
    exit 1
fi

inputFile="$1"
outputFile="$2"

sed 's/^\t.ascii\t"begin_resndrf \([0-9]\+\)"$/\tmovl\t\$\1, %edi\n\txchg\t%edi, %edi/' "$inputFile" \
| sed 's/^\t.ascii\t"end_resndrf \([0-9]\+\)"$/\tmovl\t\$-\1, %edi\n\txchg\t%edi, %edi/' \
> "$outputFile"
