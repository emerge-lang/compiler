package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue

internal val getSupertypePointers = LlvmFunction.define<LlvmPointerType<ValueArrayType<LlvmPointerType<TypeinfoType>>>>("getSupertypePointers") {
    val inputRef by param(pointerToAnyValue)
    val typeinfoPointer = getelementptr(inputRef)
        .member(AnyvalueType::typeinfo)
        .get()
        .dereference()
    val arrayPointer = getelementptr(typeinfoPointer)
        .member(TypeinfoType::supertypes)
        .get()
        .dereference()

    arrayPointer.incrementStrongReferenceCount()
    arrayPointer
}

context(LlvmFunction.BasicBlockBuilder)
internal fun LlvmValue<LlvmPointerType<out ValueArrayType<*>>>.incrementStrongReferenceCount() {
    val referenceCountPtr = getelementptr(this@incrementStrongReferenceCount)
        .member(ValueArrayType<*>::referenceCount)
        .get()

    store(
        add(referenceCountPtr.dereference(), word(1)),
        referenceCountPtr,
    )
}