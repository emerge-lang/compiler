package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.indexInLlvmStruct
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

internal class EmergeClassType private constructor(
    val context: EmergeLlvmContext,
    val structRef: LLVMTypeRef,
    val irClass: IrClass,
) : LlvmType, EmergeHeapAllocated {
    init {
        assureReinterpretableAsAnyValue(context, structRef)
    }

    override fun getRawInContext(context: LlvmContext): LLVMTypeRef {
        check(context === context)
        return structRef
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LLVMTypeRef) {
        // done in [fromLlvmStructWithoutBody]
    }

    val constructor get() = irClass.constructor.llvmRef!! as LlvmFunction<LlvmPointerType<EmergeClassType>>
    val destructor get() = irClass.destructor.llvmRef!! as LlvmFunction<LlvmVoidType>

    private val typeinfo by lazy {
        StaticAndDynamicTypeInfo.define(
            irClass.llvmName,
            emptyList(),
            { _ -> destructor },
            { emptyList() }
        )
    }

    private val anyValueBaseTemplateDynamic: LlvmGlobal<EmergeHeapAllocatedValueBaseType> by lazy {
        val constant = EmergeHeapAllocatedValueBaseType.buildConstantIn(context) {
            setValue(EmergeHeapAllocatedValueBaseType.strongReferenceCount, context.word(1))
            setValue(EmergeHeapAllocatedValueBaseType.typeinfo, typeinfo.provide(context).dynamic)
            setValue(EmergeHeapAllocatedValueBaseType.weakReferenceCollection, context.nullValue(pointerTo(EmergeWeakReferenceCollectionType)))
        }
        context.addGlobal(constant, LlvmGlobal.ThreadLocalMode.SHARED)
    }

    /**
     * The implementation of [IrAllocateObjectExpression], for objects that are supposed to be de-allocate-able (not static)
     */
    fun allocateUninitializedDynamicObject(builder: BasicBlockBuilder<EmergeLlvmContext, *>): LlvmValue<LlvmPointerType<EmergeClassType>> {
        val heapAllocation: LlvmValue<LlvmPointerType<EmergeClassType>>
        with(builder) {
            heapAllocation = heapAllocate(this@EmergeClassType)
            val basePointer = getelementptr(heapAllocation).anyValueBase().get()
            memcpy(basePointer, anyValueBaseTemplateDynamic, EmergeHeapAllocatedValueBaseType.sizeof(), false)
        }

        return heapAllocation
    }

    override fun pointerToCommonBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
        require(value.type is LlvmPointerType<*>)
        require(value.type.pointed is EmergeClassType)
        @Suppress("UNCHECKED_CAST")
        return builder.getelementptr(value as LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>)
            .stepUnsafe(builder.context.i32(0), EmergeHeapAllocatedValueBaseType)
    }

    override fun toString(): String {
        return "EmergeStruct[${irClass.fqn}]"
    }

    companion object {
        fun fromLlvmStructWithoutBody(
            context: EmergeLlvmContext,
            structRef: LLVMTypeRef,
            irClass: IrClass,
        ): EmergeClassType {
            val baseElements = listOf(
                EmergeHeapAllocatedValueBaseType
            ).map { it.getRawInContext(context) }

            irClass.memberVariables.forEachIndexed { index, member ->
                member.indexInLlvmStruct = baseElements.size + index
            }

            val emergeMemberTypesRaw = irClass.memberVariables.map { context.getReferenceSiteType(it.type).getRawInContext(context) }
            val llvmMemberTypesRaw = (baseElements + emergeMemberTypesRaw).toTypedArray()

            val llvmStructElements = PointerPointer(*llvmMemberTypesRaw)
            LLVM.LLVMStructSetBody(structRef, llvmStructElements, llvmMemberTypesRaw.size, 0)

            check(LLVM.LLVMOffsetOfElement(context.targetData.ref, structRef, 0) == 0L) {
                "Cannot reinterpret emerge type ${irClass.fqn} as Any"
            }

            return EmergeClassType(context, structRef, irClass)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        internal fun GetElementPointerStep<EmergeClassType>.anyValueBase(): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
            return stepUnsafe(context.i32(0), EmergeHeapAllocatedValueBaseType)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun GetElementPointerStep<EmergeClassType>.member(memberVariable: IrClass.MemberVariable): GetElementPointerStep<LlvmType> {
            if (memberVariable.isCPointerPointed) {
                return this as GetElementPointerStep<LlvmType>
            }

            check(memberVariable in this@member.pointeeType.irClass.memberVariables)
            return stepUnsafe(context.i32(memberVariable.indexInLlvmStruct!!), context.getReferenceSiteType(memberVariable.type))
        }
    }
}