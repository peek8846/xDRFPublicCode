###############################################################################
# Sets up the environment needed to run the xDRF pass and scripts
# Needs some manual setup
#
###############################################################################

ASSUMED_REL_DIR=.

workdir=$(pwd)

cd $PROG_LIBS/LLVM_libs
source "$workdir"/llvm-env2.sh
cd -

cd ~/Documents/Projects/MasterEx/xDRF/
source "$workdir"/xdrf-env.sh
cd -

cd ~/Documents/Libraries/pin-3.0-76991-gcc-linux/
source "$workdir"/pin-env.sh
cd -

cd $workdir
