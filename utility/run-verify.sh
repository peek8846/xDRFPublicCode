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
shift

echo "Checking..."

opt -load $VerifyXDRFSo -verify-xdrf -debug-only=VerifyXDRF-output $@ $targetFile

# echo "Checking optimistic"
# opt -load $VerifyXDRFSo -verify-xdrf -debug-only=verify-xdrf -debug-only=verify-xdrf-verbose -trace=1 $@ $targetFile
#echo "Checking conservative"
#opt -load $VerifyXDRFSo -verify-xdrf -debug-only=verify-xdrf -debug-only=verify-xdrf-verbose -trace=2 $@ $targetFile
 #echo "Checking manual"
 #opt -load $VerifyXDRFSo -verify-xdrf -debug-only=verify-xdrf -debug-only=verify-xdrf-verbose -trace=0 $@ $targetFile


#2>&1 >/dev/null \
#| python $XDRF_UTILS/verify-to-table.py
