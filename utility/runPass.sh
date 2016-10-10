
#!/bin/bash

SynchPointDelimSo=$XDRF_BUILD/SynchPointDelim/libSynchPointDelim.so
XDRFExtensionSo=$XDRF_BUILD/XDRFExtension/libXDRFExtension.so
MarkXDRFRegionsSo=$XDRF_BUILD/MarkXDRFRegions/libMarkXDRFRegions.so
VerifyXDRFSo=$XDRF_BUILD/VerifyXDRF/libVerifyXDRF.so
FlowSensitiveSo=$XDRF_BUILD/../xDRF-src/SVF-master/Release+Asserts/lib/libwpa.so
MarkRMSRegionsSo=$XDRF_BUILD/MarkRMSRegions/libMarkRMSRegions.so
ThreadDependanceSo=$XDRF_BUILD/ThreadDependantAnalysis/libThreadDependantAnalysis.so
# if [ ! -e $SynchPointDelimSo ] ; then
#     echo "Could not find SynchPointDelim pass, make sure you have setup the env and compiled the passes"
#     exit 1
# fi

llvmAAs="-scalar-evolution -basicaa -globals-aa -thread-dependence"
xdrfAs="-thread-dependence -SPDelim -XDRFextend -MarkXDRF"
svfAAs="-wpa -fspta"

#AAs="-wpa -fspta -scalar-evolution -basicaa -globals-aa"
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
    $targetFile -o .internal_temp1~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $xdrfAs -aalevel MayAlias -nousechain -trace 1 $@\
      .internal_temp1~ -o .internal_temp2~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias -nousechain -trace 2 $@\
      .internal_temp2~ -o .internal_temp1~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $svfAAs $xdrfAs -aalevel MayAlias -trace 3 $@\
      .internal_temp1~ -o .internal_temp2~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $xdrfAs -aalevel MustAlias -nousechain -trace 4 $@\
      .internal_temp2~ -o .internal_temp1~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias -nousechain -trace 5 $@\
      .internal_temp1~ -o .internal_temp2~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
      $llvmAAs $svfAAs $xdrfAs -aalevel MustAlias -trace 6 $@\
      .internal_temp2~ -o .internal_temp1~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
     $AAs -SPDelim -XDRFextend -aalevel MustAlias -ndrfconflict -MarkXDRF -trace 3 $@\
     .internal_temp3~ -o .internal_temp4~

opt -S -load $MarkXDRFRegionsSo -load $FlowSensitiveSo\
     $AAs -SPDelim -XDRFextend -aalevel MayAlias -ndrfconflict -MarkXDRF -trace 4 $@\
     .internal_temp4~ -o .internal_temp5~

opt -S \

    -load $MarkRMSRegionsSo -mark-rms .internal_temp5~ $outputFile

rm -f .internal_temp~ .internal_temp2~ .internal_temp3~ .internal_temp4~ .internal_temp5~
