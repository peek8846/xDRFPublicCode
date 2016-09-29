#!/bin/bash

PathRMSFunctionsSo=$XDRF_BUILD/PatchRMSFunctions/libPatchRMSFunctions.so

if [[ $# < 1 ]] ; then
    echo "Requires atleast one argument, the input .ll file"
    exit 1
fi

targetFile=$1


if [[ $# > 1 ]] ; then
    outputFile="-o $2"
    shift
else
    outputFile=""
fi
shift


opt -S -load $PathRMSFunctionsSo -patch-rms $targetFile $outputFile $@
