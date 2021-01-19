#
# This file is distributed under the MIT License. See LICENSE.md for details.
#

revng_add_executable(yaml-fun
  asd.cpp)

target_link_libraries(yaml-fun
  dl
  m
  revngBasicAnalyses
  revngSupport
  revngFunctionCallIdentification
  ${LLVM_LIBRARIES})
