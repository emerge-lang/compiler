package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.insertConstantInto
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

internal object LlvmWordType : LlvmCachedType(), LlvmIntegerType {
    override fun computeRaw(context: LlvmContext) = LLVM.LLVMIntTypeInContext(context.ref, LLVM.LLVMPointerSize(context.targetData) * 8)
}

internal fun LlvmContext.word(value: Int): LlvmValue<LlvmWordType> = LlvmValue(
    LLVM.LLVMConstInt(LlvmWordType.getRawInContext(this), value.toLong(), 0),
    LlvmWordType,
)

// TODO: prefix all the emerge-specific types with Emerge, so its EmergeTypeInfoType, EmergeAnyValueType, ...

internal object TypeinfoType : LlvmStructType("typeinfo") {
    val shiftRightAmount by structMember(LlvmWordType)
    val supertypes by structMember(
        pointerTo(
            ValueArrayType(
                pointerTo(this@TypeinfoType),
                this@TypeinfoType.name,
            )
        )
    )
    val vtableBlob by structMember(LlvmArrayType(0L, LlvmFunctionAddressType))
}

internal object WeakReferenceCollectionType : LlvmStructType("weakrefcoll") {
    val weakObjects = structMember(
        LlvmArrayType(10, PointerToAnyValue)
    )
    val next = structMember(pointerTo(this@WeakReferenceCollectionType))
}

internal object AnyValueType : LlvmStructType("anyvalue") {
    val strongReferenceCount by structMember(LlvmVoidType)
    val typeinfo by structMember(pointerTo(TypeinfoType))
    val weakReferenceCollection by structMember(pointerTo(WeakReferenceCollectionType))
}

internal val PointerToAnyValue: LlvmPointerType<AnyValueType> = pointerTo(AnyValueType)

/*
TODO: refactor array types to be as in the README.
Will probably leave us with just one array type where value-arrays are ArrayType<LlvmI8Type>, ...
and reference arrays are ArrayType<PointerToAnyValue>.
 */

internal class ReferenceArrayType<Element : LlvmType>(
    val elementType: Element,
) : LlvmStructType("refarray") {
    val base by structMember(AnyValueType)
    val elementCount by structMember(LlvmWordType)
    val elementsArray by structMember(LlvmArrayType(0L, elementType))
}

internal class ValueArrayType<Element : LlvmType>(
    elementType: Element,
    valueTypeName: String,
) : LlvmStructType("valuearray_$valueTypeName") {
    val strongReferenceCount by structMember(LlvmWordType)
    val weakReferenceCollection by structMember(pointerTo(WeakReferenceCollectionType))
    val elementCount by structMember(LlvmWordType)
    val elementsArray by structMember(LlvmArrayType(0L, elementType))

    fun <Raw> insertThreadLocalGlobalInto(
        context: LlvmContext,
        data: Collection<Raw>,
        rawTransform: (Raw) -> LlvmValue<Element>,
    ): LlvmValue<ValueArrayType<Element>> {
        val constValues = data.map { rawTransform(it).raw }.toTypedArray()
        val contentAsPointerPointer = PointerPointer(*constValues)
        val constantData = LLVM.LLVMConstArray2(elementsArray.type.getRawInContext(context), contentAsPointerPointer, data.size.toLong())

        val constant = insertConstantInto(context) {
            setValue(strongReferenceCount, context.word(1))
            setValue(weakReferenceCollection, context.nullValue(pointerTo(WeakReferenceCollectionType)))
            setValue(elementCount, context.word(data.size))
            setValue(elementsArray, LlvmValue(constantData, elementsArray.type))
        }

        val globalRef = LLVM.LLVMAddGlobal(context.module, this.getRawInContext(context), context.globalsScope.next())
        LLVM.LLVMSetInitializer(globalRef, constant.raw)
        LLVM.LLVMSetThreadLocal(globalRef, 1)

        return LlvmValue(globalRef, this)
    }

    companion object {
        val i8s = ValueArrayType(LlvmI8Type, "i8")
        val i16s = ValueArrayType(LlvmI16Type, "i16")
        val i32s = ValueArrayType(LlvmI32Type, "i32")
        val i64s = ValueArrayType(LlvmI64Type, "i64")
        val words = ValueArrayType(LlvmWordType, "word")
    }
}

