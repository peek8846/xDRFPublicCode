
#!/bin/bash

SynchPointDelimSo=$XDRF_BUILD/SynchPointDelim/libSynchPointDelim.so
XDRFExtensionSo=$XDRF_BUILD/XDRFExtension/libXDRFExtension.so
MarkXDRFRegionsSo=$XDRF_BUILD/MarkXDRFRegions/libMarkXDRFRegions.so
VerifyXDRFSo=$XDRF_BUILD/VerifyXDRF/libVerifyXDRF.so
FlowSensitiveSo=$XDRF_BUILD/../xDRF-src/SVF-master/Release+Asserts/lib/libwpa.so
MarkRMSRegionsSo=$XDRF_BUILD/MarkRMSRegions/libMarkRMSRegions.so
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
    -internalize -internalize-public-api-list "main" -adce -globaldce\
    $targetFile -o .internal_temp~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
    $AAs -SPDelim -XDRFextend -aalevel MustAlias -MarkXDRF -trace 1 $@\
    .internal_temp~ -o .internal_temp2~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
    $AAs -SPDelim -XDRFextend -aalevel MayAlias -MarkXDRF -trace 2 $@\
    .internal_temp2~ -o .internal_temp3~

opt -S \
    -load $MarkRMSRegionsSo -mark-rms .internal_temp3~ $outputFile

rm -f .internal_temp~ .internal_temp2~ .internal_temp3~
