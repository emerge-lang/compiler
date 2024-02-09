package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.indexInLlvmStruct
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.global.LLVM

/**
 * TODO: add the [AnyValueType] as base!!
 */
class EmergeStructType private constructor(
    val context: EmergeLlvmContext,
    val structRef: LLVMTypeRef,
    val irStruct: IrStruct,
) : LlvmType {
    override fun getRawInContext(context: LlvmContext): LLVMTypeRef {
        check(context === context)
        return structRef
    }

    companion object {
        fun fromLlvmStructWithoutBody(
            context: EmergeLlvmContext,
            structRef: LLVMTypeRef,
            irStruct: IrStruct,
        ): EmergeStructType {
            irStruct.members.forEachIndexed { index, member ->
                member.indexInLlvmStruct = index
            }

            val elements = PointerPointer(*irStruct.members.map { context.getReferenceSiteType(it.type).getRawInContext(context) }.toTypedArray())
            LLVM.LLVMStructSetBody(structRef, elements, irStruct.members.size, 0)

            return EmergeStructType(context, structRef, irStruct)
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