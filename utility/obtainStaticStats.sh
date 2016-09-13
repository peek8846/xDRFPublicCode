# APPS='apps-locks/barnes apps-locks/radiosity apps-locks/ocean/contiguous_partitions apps-locks/ocean/non_contiguous_partitions apps-locks/water-nsquared apps-locks/water-spatial apps-locks/volrend apps-locks/raytrace apps-locks/fmm'

# KERNELS='kernels-locks/fft kernels-locks/cholesky kernels-locks/lu/contiguous_blocks kernels-locks/lu/non_contiguous_blocks kernels-locks/radix'

# all="$KERNELS $APPS"

workdir=$(pwd)

trace="$1"

shift

for file in $@; do
    bash $XDRF_UTILS/run-verify.sh "$file" "$trace" 2>&1 | python $XDRF_UTILS/verifyToTable.py
done
