start="=stacked;Correctly Enclave;Incorrectly Enclave;Unaligned Enclave;Correctly Non-Enclave;Incorrectly Non-Enclave;Unaligned Non-enclave
=table
yformat=%g
ylabel=Number of regions
xlabel=Benchmark
"

outfile="$1"

shift

tofile=".temp~"
echo "$start" > "$tofile"
bash $XDRF_UTILS/obtainStaticStats.sh $@ | tr -d "," | sed "0,/lu\ /{s/lu\ /lu-contiguous /}" | sed "s/lu\ /lu-non-contiguous /" | sed "0,/ocean\ /{s/ocean\ /ocean-contiguous /}" | sed "s/ocean\ /ocean-non-contiguous /" | sed "s/spatial /water-spatial /" | sed "s/nsquared /water-nsquared /" >> "$tofile"
$PROG_LIBS/bargraph-master/bargraph.pl -pdf "$tofile" > "$outfile"
