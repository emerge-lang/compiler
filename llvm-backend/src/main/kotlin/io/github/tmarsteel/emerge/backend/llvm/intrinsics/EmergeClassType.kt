package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.indexInLlvmStruct
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes

internal class EmergeClassType private constructor(
    val context: EmergeLlvmContext,
    val structRef: LlvmTypeRef,
    val irClass: IrClass,
) : LlvmType, EmergeHeapAllocated {
    init {
        assureReinterpretableAsAnyValue(context, structRef)
    }

    override fun getRawInContext(context: LlvmContext): LlvmTypeRef {
        check(context === context)
        return structRef
    }

    override fun assureReinterpretableAsAnyValue(context: LlvmContext, selfInContext: LlvmTypeRef) {
        // done in [fromLlvmStructWithoutBody]
    }

    val constructor get() = irClass.constructor.llvmRef!! as LlvmFunction<LlvmPointerType<EmergeClassType>>
    val destructor get() = irClass.destructor.llvmRef!! as LlvmFunction<LlvmVoidType>

    private val typeinfoProvider by lazy {
        StaticAndDynamicTypeInfo.define(
            irClass.llvmName,
            emptyList(),
            { _ -> destructor },
            virtualFunctions = {
                irClass.memberFunctions
                    .asSequence()
                    .flatMap { it.overloads }
                    .filter { it.supportsDynamicDispatch }
                    .flatMap { memberFn -> memberFn.signatureHashes.map { hash -> Pair(hash, memberFn.llvmRef!!) } }
                    .associate { it }
            }
        )
    }

    /**
     * The implementation of [IrAllocateObjectExpression], for objects that are supposed to be de-allocate-able (not static)
     */
    fun allocateUninitializedDynamicObject(builder: BasicBlockBuilder<EmergeLlvmContext, *>): LlvmValue<LlvmPointerType<EmergeClassType>> {
        val typeinfo = try {
            typeinfoProvider.provide(context)
        } catch (ex: VirtualFunctionHashCollisionException) {
            throw VirtualFunctionHashCollisionException("Type ${irClass.canonicalName}: ${ex.message}", ex)
        }

        val heapAllocation: LlvmValue<LlvmPointerType<EmergeClassType>>
        with(builder) {
            heapAllocation = heapAllocate(this@EmergeClassType)
            val basePointer = getelementptr(heapAllocation).anyValueBase().get()
            store(
                context.word(1),
                getelementptr(basePointer)
                    .member { this.strongReferenceCount }
                    .get()
            )
            store(
                typeinfo.dynamic,
                getelementptr(basePointer)
                    .member { this.typeinfo }
                    .get()
            )
            store(
                context.nullValue(pointerTo(EmergeWeakReferenceCollectionType)),
                getelementptr(basePointer)
                    .member { this.weakReferenceCollection }
                    .get()
            )
        }

        return heapAllocation
    }

    private var llvmStructMembersDefined = false
    fun assureLlvmStructMembersDefined() {
        if (llvmStructMembersDefined) {
            return
        }
        llvmStructMembersDefined = true

        val baseElements = listOf(
            EmergeHeapAllocatedValueBaseType
        ).map { it.getRawInContext(context) }

        irClass.memberVariables.forEachIndexed { index, member ->
            member.indexInLlvmStruct = baseElements.size + index
        }

        val emergeMemberTypesRaw = irClass.memberVariables.map { context.getReferenceSiteType(it.type).getRawInContext(context) }
        NativePointerArray.fromJavaPointers(baseElements + emergeMemberTypesRaw).use { llvmMemberTypesRaw ->
            Llvm.LLVMStructSetBody(structRef, llvmMemberTypesRaw, llvmMemberTypesRaw.length, 0)
        }

        check(Llvm.LLVMOffsetOfElement(context.targetData.ref, structRef, 0) == 0L) {
            "Cannot reinterpret emerge type ${irClass.canonicalName} as Any"
        }
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
        return "EmergeStruct[${irClass.canonicalName}]"
    }

    companion object {
        fun fromLlvmStructWithoutBody(
            context: EmergeLlvmContext,
            structRef: LlvmTypeRef,
            irClass: IrClass,
        ): EmergeClassType {
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