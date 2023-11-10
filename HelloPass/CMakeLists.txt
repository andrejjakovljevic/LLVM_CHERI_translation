cmake_minimum_required(VERSION 3.16)
add_llvm_library( HelloPass MODULE
  HelloPass.cpp
  PLUGIN_TOOL
  opt
  )
