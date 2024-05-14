package io.github.tmarsteel.emerge.backend.llvm.dsl

import com.sun.jna.ptr.NativeLongByReference
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm

data class LlvmFunction<out R : LlvmType>(
    val address: LlvmConstant<LlvmFunctionAddressType>,
    val type: LlvmFunctionType<R>,
) {
    val name: String get() {
        val lengthRef = NativeLongByReference()
        val nameCharsPtr = Llvm.LLVMGetValueName2(address.raw, lengthRef)
        val nameBytes = nameCharsPtr.getByteArray(0, lengthRef.value.toInt())
        return String(nameBytes)
    }
}