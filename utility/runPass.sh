#!/bin/bash

OPT="$LLVM_3_8_0_BIN/opt"

SynchPointDelimSo="$XDRF_BUILD/SynchPointDelim/libSynchPointDelim.so"
XDRFExtensionSo="$XDRF_BUILD/XDRFExtension/libXDRFExtension.so"
MarkXDRFRegionsSo="$XDRF_BUILD/MarkXDRFRegions/libMarkXDRFRegions.so"
VerifyXDRFSo="$XDRF_BUILD/VerifyXDRF/libVerifyXDRF.so"
FlowSensitiveSo="$XDRF_BUILD/../xDRF-src/SVF-master/Release+Asserts/lib/libwpa.so"
MarkRMSRegionsSo="$XDRF_BUILD/MarkRMSRegions/libMarkRMSRegions.so"
ThreadDependanceSo="$XDRF_BUILD/ThreadDependence/libThreadDependence.so"
# if [ ! -e $SynchPointDelimSo ] ; then
#     echo "Could not find SynchPointDelim pass, make sure you have setup the env and compiled the passes"
#     exit 1
# fi

llvmAAs="-scalar-evolution -basicaa -globals-aa -tbaa -scev-aa"
#llvmAAs="-disable-basicaa"
svfAAs="-wpa -fspta"
xdrfAs="-thread-dependence -SPDelim -XDRFextend -MarkXDRF"

#AAs="-wpa -fspta -scalar-evolution -basicaa -globals-aa"
#AAs="-basicaa -globals-aa"

if [[ $# < 1 ]] ; then
    echo "Requires atleast one argument, the input .ll file"
    exit 1
fi

targetFile=$1

if [[ $# > 1 ]] ; then
    outputFile="$2"
    shift
else
    outputFile=""
fi
shift


TMPLL=$(mktemp -t xDRF-internal.XXXXXXXXXX)
if [ $? -ne 0 ]; then
    exit 1
fi

CALL_OPT() {
    # This function will perform a call to "$OPT -S" with the given
    # parameters to the function. It will use $TMPLL as input,
    # internally save the output to another file and then move
    # the output to $TMPLL for easy chaining.

    local TMPOUT=$(mktemp -t xDRF-internal.XXXXXXXXXX)
    if [ $? -ne 0 ]; then
        rm -f "$TMPLL"
        exit 1
    fi

    echo "OPT ARGS:" "$@"
    "$OPT" -S "$@" "$TMPLL" -o "$TMPOUT"
    mv "$TMPOUT" "$TMPLL"
}

CALL_OPT_XDRF() {
    # Convenience for loading relevant passes
    CALL_OPT -load "$FlowSensitiveSo" -load "$MarkXDRFRegionsSo" "$@"
}

# Copy to temporary file
cp "$targetFile" "$TMPLL"

# Run the initial passes
CALL_OPT -internalize -internalize-public-api-list "main" -adce -globaldce

# Standard approach
CALL_OPT_XDRF $llvmAAs         $xdrfAs -aalevel MayAlias  -nousechain -trace 1 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias  -nousechain -trace 2 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias              -trace 3 "$@"
CALL_OPT_XDRF $llvmAAs         $xdrfAs -aalevel MustAlias -nousechain -trace 4 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias -nousechain -trace 5 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias             -trace 6 "$@"

# CRA appraoch
CALL_OPT_XDRF $llvmAAs         $xdrfAs -aalevel MayAlias  -nousechain -ndrfconflict -trace  7 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias  -nousechain -ndrfconflict -trace  8 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias              -ndrfconflict -trace  9 "$@"
CALL_OPT_XDRF $llvmAAs         $xdrfAs -aalevel MustAlias -nousechain -ndrfconflict -trace 10 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias -nousechain -ndrfconflict -trace 11 "$@"
CALL_OPT_XDRF $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias             -ndrfconflict -trace 12 "$@"

# RMS marking
CALL_OPT -load "$MarkRMSRegionsSo" -mark-rms

# Move temporary file to output
if [ -n "$outputFile" ] ; then
    cp --no-preserve=mode "$TMPLL" "$outputFile"
else
    cat "$TMPLL"
fi
rm -f "$TMPLL"
