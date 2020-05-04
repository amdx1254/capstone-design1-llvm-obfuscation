add_llvm_library( LLVMObfuscation MODULE
  ReturnObfuscation.cpp

 DEPENDS
 intrinsics_gen
 PLUGIN_TOOL
 opt
  )