for D in *;
do
    if [ -d "${D}" ]; then
	cd $D
	exec=${D#*/}
	exec=$(echo $exec | tr '[:lower:]' '[:upper:]')
	exec="$exec".xDRF.ll
	if [[ ! -e $exec ]]; then
	    echo "$exec not previously compiled, so cannot be patched"
	else
	    bash $XDRF_UTILS/patchXDRF.sh $exec
	fi
	cd ..
    fi
done
