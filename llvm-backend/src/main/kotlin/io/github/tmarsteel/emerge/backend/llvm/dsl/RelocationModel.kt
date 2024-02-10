package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

enum class RelocationModel(val numeric: Int) {
    STATIC(LLVM.LLVMRelocStatic),
    PIC(LLVM.LLVMRelocPIC),
    DYNAMIC_NO_PIC(LLVM.LLVMRelocDynamicNoPic),
    ROPI(LLVM.LLVMRelocROPI),
    RWPI(LLVM.LLVMRelocRWPI),
    ROPI_RWPI(LLVM.LLVMRelocROPI_RWPI),
}