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

cd ~/Documents/Projects/MasterEx/pintool
source "$workdir"/pin-env.sh
cd -

cd $workdir
