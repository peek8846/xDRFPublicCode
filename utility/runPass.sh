
#!/bin/bash

SynchPointDelimSo=$XDRF_BUILD/SynchPointDelim/libSynchPointDelim.so
XDRFExtensionSo=$XDRF_BUILD/XDRFExtension/libXDRFExtension.so
MarkXDRFRegionsSo=$XDRF_BUILD/MarkXDRFRegions/libMarkXDRFRegions.so
VerifyXDRFSo=$XDRF_BUILD/VerifyXDRF/libVerifyXDRF.so
FlowSensitiveSo=$XDRF_BUILD/../xDRF-src/SVF-master/Release+Asserts/lib/libwpa.so
# if [ ! -e $SynchPointDelimSo ] ; then
#     echo "Could not find SynchPointDelim pass, make sure you have setup the env and compiled the passes"
#     exit 1
# fi

AAs="-wpa -fspta"
#AAs="-basicaa -globals-aa"

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


opt -S \
    -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
    -internalize -internalize-public-api-list "main" -adce -globaldce $AAs -SPDelim -XDRFextend -MarkXDRF $@\
    $targetFile $outputFile
