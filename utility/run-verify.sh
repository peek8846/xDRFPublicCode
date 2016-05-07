#!/bin/bash

VerifyXDRFSo=$XDRF_BUILD/VerifyXDRF/libVerifyXDRF.so

if [ ! -e $VerifyXDRFSo ] ; then
    echo "Could not find VerifyXDRF pass, make sure you have setup the env and compiled the passes"
    exit 1
fi

if [[ $# < 1 ]] ; then
    echo "Requires one argument, the input .ll file"
    exit 1
fi

targetFile=$1

opt -load $VerifyXDRFSo -verify-xdrf -debug-only=verify-xdrf -debug-only=verify-xdrf-verbose $targetFile


#2>&1 >/dev/null \
#| python $XDRF_UTILS/verify-to-table.py
