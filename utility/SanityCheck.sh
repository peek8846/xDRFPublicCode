input=$1
numBeginNDRF0=$(grep "begin_NDRF(i32 0)" $input | wc -l)
numBeginNDRF1=$(grep "begin_NDRF(i32 1)" $input | wc -l)
numEndNDRF0=$(grep "end_NDRF(i32 0)" $input | wc -l)
numEndNDRF1=$(grep "end_NDRF(i32 1)" $input | wc -l)
numBeginXDRF0=$(grep "begin_XDRF(i32 0)" $input | wc -l)
numBeginXDRF1=$(grep "begin_XDRF(i32 1)" $input | wc -l)
numEndXDRF0=$(grep "end_XDRF(i32 0)" $input | wc -l)
numEndXDRF1=$(grep "end_XDRF(i32 1)" $input | wc -l)
numBeginEncRMS=$(grep "RMS_Initial_Acq" $input | grep "i32 1" | wc -l)
numEndEncRMS=$(grep "RMS_Final_Release" $input | grep "i32 1" | wc -l)
numBeginNEncRMS=$(grep "RMS_Initial_Acq" $input | grep "i32 0" | wc -l)
numEndNEncRMS=$(grep "RMS_Final_Release" $input | grep "i32 0" | wc -l)
numBarrRMS=$(grep "RMS_Initial_Barrier" $input | grep -v "declare" | wc -l)

echo "Trace 0 (compiler)"
echo "begin_NDRF:$numBeginNDRF0"
echo "end_NDRF:$numEndNDRF0"
echo "begin_XDRF:$numBeginXDRF0"
echo "end_XDRF:$numEndXDRF0"
echo "Trace 1 (converted manual)"
echo "begin_NDRF:$numBeginNDRF1"
echo "end_NDRF:$numEndNDRF1"
echo "begin_XDRF:$numBeginXDRF1"
echo "end_XDRF:$numEndXDRF1"
echo "Manual Markings (not including joins)"
echo "acq EncNDRF:$numBeginEncRMS"
echo "rel EncNDRF:$numEndEncRMS"
echo "acq NDRF:$numBeginNEncRMS"
echo "rel NDRF:$numEndNEncRMS"
echo "Barriers:$numBarrRMS"

