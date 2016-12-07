cmake_minimum_required(VERSION 2.8.12.2)

find_package(LLVM REQUIRED CONFIG)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
include_directories(./SVF-master/include)

set(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -std=c++11 -Wall")
set(CMAKE_BUILD_TYPE Debug)

#add_subdirectory(SynchPointDelim)
add_subdirectory(XDRFExtension)
add_subdirectory(MarkXDRFRegions)
add_subdirectory(MarkRMSRegions)
add_subdirectory(PatchRMSFunctions)
add_subdirectory(VerifyXDRF)
add_subdirectory(ThreadDependenceAnalysis)
add_subdirectory(MemDepPrinter)
