#!/bin/bash

if [[ $# < 2 ]] ; then
    echo "Requires at least two argument, the input .s file and the output .s file."
    exit 1
fi

inputFile="$1"
outputFile="$2"

sed '
  /^\t#APP$/{
    N
    N
    s/\t#APP\n\t.ascii\t"begin_resndrf \([0-9]\+\)"\n\t#NO_APP\n/\tmovl\t\$\1, %edi\n\txorl\t%eax, %eax\n\tcallq\tbegin_NDRF\n/
  }' "$inputFile" \
> "$outputFile"
