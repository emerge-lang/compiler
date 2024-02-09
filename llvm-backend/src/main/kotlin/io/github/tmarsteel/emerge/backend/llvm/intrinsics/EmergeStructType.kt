package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.ParameterDelegate
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.indexInLlvmStruct
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

/**
 * TODO: add the [AnyValueType] as base!!
 */
internal class EmergeStructType private constructor(
    val context: EmergeLlvmContext,
    val structRef: LLVMTypeRef,
    val irStruct: IrStruct,
) : LlvmType, EmergeHeapAllocated {
    override fun getRawInContext(context: LlvmContext): LLVMTypeRef {
        check(context === context)
        return structRef
    }

    private val typeinfo = StaticAndDynamicTypeInfo.define(
        irStruct.llvmName,
        emptyList(),
        KotlinLlvmFunction.define(
            "${irStruct.llvmName}__finalize",
            LlvmVoidType,
        ) {
            // TODO: iterate members, decrement refcount, potentiall invoke the deallocator
        },
        { emptyList() }
    )

    private val anyValueBaseTemplateDynamic: LlvmGlobal<AnyValueType> by lazy {
        val constant = AnyValueType.buildConstantIn(context) {
            setValue(AnyValueType.strongReferenceCount, context.word(1))
            setValue(AnyValueType.typeinfo, typeinfo.provide(context).dynamic)
            setValue(AnyValueType.weakReferenceCollection, context.nullValue(pointerTo(WeakReferenceCollectionType)))
        }
        context.addGlobal(constant, LlvmGlobal.ThreadLocalMode.SHARED)
    }

    private val defaultConstructorIr: IrFunction = irStruct.constructors.overloads.single()
    val defaultConstructor: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<EmergeStructType>> = KotlinLlvmFunction.define(
        defaultConstructorIr.llvmName,
        pointerTo(this),
    ) {
        val params: List<Pair<IrStruct.Member, ParameterDelegate<*>>> = defaultConstructorIr.parameters.map { irParam ->
            val member = irStruct.members.single { it.name == irParam.name }
            member to param(context.getReferenceSiteType(irParam.type))
        }

        body {
            val heapAlloc = heapAllocate(this@EmergeStructType)
            val basePointer = getelementptr(heapAlloc).anyValueBase().get()
            memcpy(basePointer, anyValueBaseTemplateDynamic, AnyValueType.sizeof())
            for ((irStructMember, llvmParam) in params) {
                val memberPointer = getelementptr(heapAlloc).member(irStructMember).get()
                val paramValue = llvmParam.getValue(null, String::length)
                store(paramValue, memberPointer)
                if (paramValue.type is LlvmPointerType<*> && paramValue.type.pointed is EmergeHeapAllocated) {
                    @Suppress("UNCHECKED_CAST")
                    (paramValue as LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>).incrementStrongReferenceCount()
                }
            }
            ret(heapAlloc)
        }
    }

    override fun pointerToAnyValueBase(
        builder: BasicBlockBuilder<*, *>,
        value: LlvmValue<*>
    ): GetElementPointerStep<AnyValueType> {
        require(value.type is LlvmPointerType<*>)
        require(value.type.pointed is EmergeStructType)
        @Suppress("UNCHECKED_CAST")
        return builder.getelementptr(value as LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>)
            .stepUnsafe(builder.i32(0), AnyValueType)
    }

    companion object {
        fun fromLlvmStructWithoutBody(
            context: EmergeLlvmContext,
            structRef: LLVMTypeRef,
            irStruct: IrStruct,
        ): EmergeStructType {
            val baseElements = listOf(
                AnyValueType
            ).map { it.getRawInContext(context) }

            irStruct.members.forEachIndexed { index, member ->
                member.indexInLlvmStruct = baseElements.size + index
            }

            val emergeMemberTypesRaw = irStruct.members.map { context.getReferenceSiteType(it.type).getRawInContext(context) }
            val llvmMemberTypesRaw = (baseElements + emergeMemberTypesRaw).toTypedArray()

            val llvmStructElements = PointerPointer(*llvmMemberTypesRaw)
            LLVM.LLVMStructSetBody(structRef, llvmStructElements, llvmMemberTypesRaw.size, 0)

            return EmergeStructType(context, structRef, irStruct)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        internal fun GetElementPointerStep<EmergeStructType>.anyValueBase(): GetElementPointerStep<AnyValueType> {
            return stepUnsafe(i32(0), AnyValueType)
        }

        context(BasicBlockBuilder<EmergeLlvmContext, *>)
        fun GetElementPointerStep<EmergeStructType>.member(member: IrStruct.Member): GetElementPointerStep<LlvmType> {
            if (member.isCPointerPointed) {
                return this as GetElementPointerStep<LlvmType>
            }

            check(member in this@member.pointeeType.irStruct.members)
            return stepUnsafe(i32(member.indexInLlvmStruct!!), context.getAllocationSiteType(member.type))
        }
    }
}