package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

enum class RelocationModel(val numeric: Int) {
    /** Non-relocatable code */
    STATIC(LLVM.LLVMRelocStatic),
    /** Fully relocatable, position independent code */
    POSITION_INDEPENDENT(LLVM.LLVMRelocPIC),
    /** Relocatable external references, non-relocatable code **/
    RELOCATABLE_EXTERNAL_REFERENCES(LLVM.LLVMRelocDynamicNoPic),
    /** Code and read-only data relocatable, accessed PC-relative */
    ROPI(LLVM.LLVMRelocROPI),
    /** Read-write data relocatable, accessed relative to static base */
    RWPI(LLVM.LLVMRelocRWPI),
    /** Combination of ropi and rwpi */
    ROPI_RWPI(LLVM.LLVMRelocROPI_RWPI),

    DEFAULT(LLVM.LLVMRelocDefault)
}