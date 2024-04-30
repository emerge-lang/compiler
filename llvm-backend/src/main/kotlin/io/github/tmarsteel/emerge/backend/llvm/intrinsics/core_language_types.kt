package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmCachedType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

internal object EmergeWordType : LlvmCachedType(), LlvmIntegerType {
    override fun computeRaw(context: LlvmContext) = LLVM.LLVMIntTypeInContext(context.ref, context.targetData.pointerSizeInBytes * 8)
    override fun toString() = "%word"
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

internal fun LlvmContext.word(value: ULong): LlvmConstant<EmergeWordType> = word(value.toLong())

internal object EmergeAnyValueVirtualsType : LlvmStructType("anyvalue_virtuals") {
    val finalizeFunction by structMember(LlvmFunctionAddressType)

    val finalizeFunctionType = LlvmFunctionType(LlvmVoidType, emptyList())
}

internal val PointerToAnyEmergeValue: LlvmPointerType<EmergeHeapAllocatedValueBaseType> = pointerTo(EmergeHeapAllocatedValueBaseType)

internal object EmergeWeakReferenceCollectionType : LlvmStructType("weakrefcoll") {
    val weakObjects by structMember(
        LlvmArrayType(10, PointerToAnyEmergeValue),
    )
    val next by structMember(pointerTo(this@EmergeWeakReferenceCollectionType))
}

/**
 * The data common to all heap-allocated objects in emerge
 */
internal object EmergeHeapAllocatedValueBaseType : LlvmStructType("anyvalue"), EmergeHeapAllocated {
    val strongReferenceCount by structMember(EmergeWordType)
    val typeinfo by structMember(pointerTo(TypeinfoType.GENERIC))
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