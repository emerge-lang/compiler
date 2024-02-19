package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFixedIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmInlineStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

internal object EmergeWordType : LlvmCachedType(), LlvmIntegerType {
    override fun computeRaw(context: LlvmContext) = LLVM.LLVMIntTypeInContext(context.ref, context.targetData.pointerSizeInBytes * 8)
}

internal fun LlvmContext.word(value: Int): LlvmConstant<EmergeWordType> {
    val wordMax = EmergeWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        LLVM.LLVMConstInt(EmergeWordType.getRawInContext(this), value.toLong(), 0),
        EmergeWordType,
    )
}

internal fun LlvmContext.word(value: Long): LlvmConstant<EmergeWordType> {
    val wordMax = EmergeWordType.getMaxUnsignedValueInContext(this)
    check (value.toBigInteger() <= wordMax) {
        "The value $value cannot be represented by the word type on this target (max $wordMax)"
    }

    return LlvmConstant(
        LLVM.LLVMConstInt(EmergeWordType.getRawInContext(this), value, 0),
        EmergeWordType,
    )
}

internal object EmergeAnyValueVirtualsType : LlvmStructType("anyvalue_virtuals") {
    val dropFunction by structMember(LlvmFunctionAddressType)

    val dropFunctionType = LlvmFunctionType(LlvmVoidType, emptyList())
}

internal val PointerToAnyEmergeValue: LlvmPointerType<EmergeHeapAllocatedValueBaseType> = pointerTo(EmergeHeapAllocatedValueBaseType)

internal object EmergeWeakReferenceCollectionType : LlvmStructType("weakrefcoll") {
    val weakObjects = structMember(
        LlvmArrayType(10, pointerTo(EmergeHeapAllocatedValueBaseType))
    )
    val next = structMember(pointerTo(this@EmergeWeakReferenceCollectionType))
}

/**
 * The data common to all heap-allocated objects in emerge
 */
internal object EmergeHeapAllocatedValueBaseType : LlvmStructType("anyvalue"), EmergeHeapAllocated {
    val strongReferenceCount by structMember(EmergeWordType)
    val typeinfo by structMember(pointerTo(TypeinfoType))
    val weakReferenceCollection by structMember(pointerTo(EmergeWeakReferenceCollectionType))

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>,
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        return builder.getelementptr(value.reinterpretAs(PointerToAnyEmergeValue))
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        // this is AnyValue itself, noop
    }
}

internal interface EmergeHeapAllocated : LlvmType {
    fun pointerToCommonBase(builder: BasicBlockBuilder<*, *>, value: LlvmValue<*>): GetElementPointerStep<EmergeHeapAllocatedValueBaseType>

    /**
     * This abstract method is a reminder to check *at emerge compile time* that your subtype of [EmergeHeapAllocated]#
     * can actually be [LlvmValue.reinterpretAs] any([EmergeHeapAllocatedValueBaseType]).
     * @throws CodeGenerationException if that is not the case.
     */
    fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef)
}

// TODO: move to array_types.kt
internal object EmergeArrayBaseType : LlvmStructType("anyarray"), EmergeHeapAllocated {
    val anyBase by structMember(EmergeHeapAllocatedValueBaseType)
    val elementCount by structMember(EmergeWordType)

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        with(builder) {
            return getelementptr(value.reinterpretAs(pointerTo(this@EmergeArrayBaseType))).member { anyBase }
        }
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        check(LLVM.LLVMOffsetOfElement(context.targetData.ref, selfInContext, anyBase.indexInStruct) == 0L)
    }
}

internal class EmergeArrayType<Element : LlvmType>(
    val elementType: Element,
    /**
     * Has to return typeinfo that suits for an Array<E>. This is so boxed types can supply their type-specific virtual functions
     */
    private val typeinfo: StaticAndDynamicTypeInfo.Provider,
    typeNameSuffix: String = typeNameSuffix(elementType),
) : LlvmStructType("array_$typeNameSuffix"), EmergeHeapAllocated {
    val base by structMember(EmergeArrayBaseType)
    val elements by structMember(LlvmArrayType(0L, elementType))

    override fun computeRaw(context: LlvmContext): LLVMTypeRef {
        val raw = super.computeRaw(context)
        assureReinterpretableAsAnyValue(context, raw)
        return raw
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        check(LLVM.LLVMOffsetOfElement(context.targetData.ref, selfInContext, base.indexInStruct) == 0L)
    }

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        check(value.type is LlvmPointerType<*>)
        with(builder) {
            return getelementptr(value.reinterpretAs(pointerTo(this@EmergeArrayType)))
                .member { base }
                .member { anyBase }
        }
    }

    fun <Raw> buildConstantIn(
        context: EmergeLlvmContext,
        data: Collection<Raw>,
        rawTransform: (Raw) -> LlvmValue<Element>,
    ): LlvmConstant<LlvmInlineStructType> {
        /*
        there is a problem with constant arrays of the dynamic-array format of emerge:
        array types are declared with [0 x %element] so no space is wasted but getelementptr access
        is well defined. However, declaring a constant "Hello World" string directly against an
        array type is not valid:

        @myString = global %array_i8 { %anyarray { %anyvalue { ... }, i64 11 }, [11 x i8] c"Hello World" }

        LLVM will complain that we put an [13 x i8] where a [0 x i8] should go.
        The solution: declare the global as what it is, but use %array_i8 when referring to it:

        @myString = global { %anyarray, [11 x i8] } { %anyarray { %anyvalue { ... }, i64 11 }, [11 x i8] c"Hello World" }

        and when referring to it:

        define i8 @access_string_constant(i64 %index) {
        entry:
            %elementPointer = getelementptr %array_i8, ptr @myString, i32 0, i32 1, i64 %index
            %value = load i8, ptr %elementPointer
            ret i8 %value
        }

        Hence: here, we don't use ArrayType.buildConstantIn, but hand-roll it to do the typing trick
         */

        val anyArrayBaseConstant = EmergeArrayBaseType.buildConstantIn(context) {
            setValue(EmergeArrayBaseType.anyBase, EmergeHeapAllocatedValueBaseType.buildConstantIn(context) {
                setValue(EmergeHeapAllocatedValueBaseType.strongReferenceCount, context.word(1))
                setValue(EmergeHeapAllocatedValueBaseType.typeinfo, typeinfo.provide(context).static)
                setValue(
                    EmergeHeapAllocatedValueBaseType.weakReferenceCollection,
                    context.nullValue(pointerTo(EmergeWeakReferenceCollectionType))
                )
            })
            setValue(EmergeArrayBaseType.elementCount, context.word(data.size))
        }
        val payload = LlvmArrayType(data.size.toLong(), elementType).buildConstantIn(
            context,
            data.map { rawTransform(it) },
        )

        val inlineConstant = LlvmInlineStructType.buildInlineTypedConstantIn(
            context,
            anyArrayBaseConstant,
            payload
        )

        val anyArrayBaseOffsetInGeneralType = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            base.indexInStruct,
        )
        val anyArrayBaseOffsetInConstant = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            0,
        )
        check(anyArrayBaseOffsetInConstant == anyArrayBaseOffsetInGeneralType)

        val firstElementOffsetInGeneralType = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            this.getRawInContext(context),
            1,
        )
        val firstElementOffsetInConstant = LLVM.LLVMOffsetOfElement(
            context.targetData.ref,
            inlineConstant.type.getRawInContext(context),
            1,
        )
        check(firstElementOffsetInConstant == firstElementOffsetInGeneralType)

        return inlineConstant
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
            elementType is EmergeWordType -> "word"
            elementType is LlvmPointerType<*> && (elementType.pointed == LlvmVoidType) -> "ptr"
            elementType is LlvmPointerType<*> && (elementType.pointed is EmergeArrayBaseType || elementType.pointed is EmergeStructType) -> "ref"
            else -> throw IllegalArgumentException("The LLVM array-type suffix for element type $elementType is not defined")
        }
    }
}
