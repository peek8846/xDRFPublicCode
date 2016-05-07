sed -r -i '/.*call.*void.*@RMS_Initial_Acq\(.*, i32 0\).*/ a \ \ call void (...) @end_XDRF(i32 1)\n  call void (...) @begin_NDRF(i32 1)' $1 
sed -r -i '/.*call.*void.*@RMS_Final_Release.*\(i32 0\).*/ a \ \ call void (...) @end_NDRF(i32 1)\n  call void (...) @begin_XDRF(i32 1)' $1
sed -r -i '/.*call.*void.*@RMS_Initial_Barrier.*/ a \ \ call void (...) @end_XDRF(i32 1)\n  call void (...) @begin_NDRF(i32 1)' $1 
sed -r -i '/.*call.*void.*@RMS_Final_Barrier.*/ a \ \ call void (...) @end_NDRF(i32 1)\n  call void (...) @begin_XDRF(i32 1)' $1
sed -r -i '/.*call.*void.*@RMS_Initial_Acq\(.*, i32 1\).*/ a \ \ call void (...) @begin_NDRF(i32 1)' $1
sed -r -i '/.*call.*void.*@RMS_Final_Release.*\(i32 1\).*/ a \ \ call void (...) @end_NDRF(i32 1)' $1
