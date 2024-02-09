/**
 * TODO: rename file to core_language_types
 */
package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFixedIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.global.LLVM

internal object LlvmWordType : LlvmCachedType(), LlvmIntegerType {
    override fun computeRaw(context: LlvmContext) = LLVM.LLVMIntTypeInContext(context.ref, LLVM.LLVMPointerSize(context.targetData) * 8)
}

internal fun LlvmContext.word(value: Int): LlvmConstant<LlvmWordType> {
    val wordMax = LlvmWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        LLVM.LLVMConstInt(LlvmWordType.getRawInContext(this), value.toLong(), 0),
        LlvmWordType,
    )
}

internal fun LlvmContext.word(value: Long): LlvmConstant<LlvmWordType> {
    val wordMax = LlvmWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        LLVM.LLVMConstInt(LlvmWordType.getRawInContext(this), value, 0),
        LlvmWordType,
    )
}

// TODO: prefix all the emerge-specific types with Emerge, so its EmergeTypeInfoType, EmergeAnyValueType, ...

internal object AnyValueVirtualsType : LlvmStructType("anyvalue_virtuals") {
    val dropFunction by structMember(LlvmFunctionAddressType)
}

internal val PointerToAnyValue: LlvmPointerType<AnyValueType> = pointerTo(AnyValueType)

internal object WeakReferenceCollectionType : LlvmStructType("weakrefcoll") {
    val weakObjects = structMember(
        LlvmArrayType(10, pointerTo(AnyValueType))
    )
    val next = structMember(pointerTo(this@WeakReferenceCollectionType))
}

internal object AnyValueType : LlvmStructType("anyvalue") {
    val strongReferenceCount by structMember(LlvmWordType)
    val typeinfo by structMember(pointerTo(TypeinfoType))
    val weakReferenceCollection by structMember(pointerTo(WeakReferenceCollectionType))
}

internal object AnyArrayType : LlvmStructType("anyarray") {
    val anyBase by structMember(AnyValueType)
    val elementCount by structMember(LlvmWordType)
}

internal class ArrayType<Element : LlvmType>(
    val elementType: Element,
    /**
     * Has to return typeinfo that suits for an Array<E>. This is so boxed types can supply their type-specific virtual functions
     */
    private val typeinfo: StaticAndDynamicTypeInfo.Provider,
    typeNameSuffix: String = typeNameSuffix(elementType),
) : LlvmStructType("array_$typeNameSuffix") {
    val base by structMember(AnyArrayType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    fun <Raw> buildConstantIn(
        context: EmergeLlvmContext,
        data: Collection<Raw>,
        rawTransform: (Raw) -> LlvmValue<Element>,
    ): LlvmConstant<ArrayType<Element>> {
        val constValues = data.map { rawTransform(it).raw }.toTypedArray()
        val contentAsPointerPointer = PointerPointer(*constValues)
        val constantData = LLVM.LLVMConstArray2(elements.type.getRawInContext(context), contentAsPointerPointer, data.size.toLong())

        return buildConstantIn(context) {
            setValue(base, AnyArrayType.buildConstantIn(context) {
                setValue(AnyArrayType.anyBase, AnyValueType.buildConstantIn(context) {
                    setValue(AnyValueType.strongReferenceCount, context.word(1))
                    setValue(AnyValueType.typeinfo, typeinfo.provide(context).static)
                    setValue(AnyValueType.weakReferenceCollection, context.nullValue(pointerTo(WeakReferenceCollectionType)))
                })
                setValue(AnyArrayType.elementCount, context.word(data.size))
            })
            setValue(elements, LlvmValue(constantData, elements.type))
        }
    }

    companion object {
        val VIRTUAL_FUNCTION_HASH_GET_ELEMENT: Long = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
        val VIRTUAL_FUNCTION_HASH_SET_ELEMENT: Long = 0b0100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

        /**
         * @return the suffix for the llvm type, based on the array elements. E.g. `i32` or `ptr`
         * @throws IllegalArgumentException if the suffix is not defined for the element type.
         */
        fun typeNameSuffix(elementType: LlvmType): String = when {
            elementType is LlvmFixedIntegerType -> "i${elementType.nBits}"
            elementType is LlvmWordType -> "word"
            elementType is LlvmPointerType<*> && (elementType.pointed == LlvmVoidType) -> "ptr"
            elementType is LlvmPointerType<*> && (elementType.pointed is AnyArrayType || elementType.pointed is EmergeStructType) -> "ref"
            else -> throw IllegalArgumentException("The LLVM array-type suffix for element type $elementType is not defined")
        }
    }
}
