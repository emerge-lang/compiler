package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.i32
import org.bytedeco.llvm.LLVM.LLVMValueRef
import kotlin.reflect.KProperty1

sealed class GetElementPointerStep<P : LlvmType> private constructor(
    private val pointeeType: P,
) {
    private var consumed = false

    private fun consume() {
        check(!consumed) {
            "This instance of ${this::class.simpleName} was not used with strict method-chaining."
        }
        consumed = true
    }

    private fun <NewP : LlvmType> step(index: LlvmValue<LlvmIntegerType>, pointeeType: NewP): GetElementPointerStep<NewP> {
        consume()
        return Subsequent(this, index, pointeeType)
    }

    /**
     * @return first: the base pointer, second: the list of indices being traversed, third: the type the resulting pointer points to
     */
    internal fun completeAndGetData(): Triple<LlvmValue<LlvmPointerType<*>>, List<LLVMValueRef>, P> {
        consume()
        val indices = ArrayList<LLVMValueRef>()
        var pivot: GetElementPointerStep<*> = this
        while (pivot is Subsequent<*>) {
            indices.add(0, pivot.index.raw)
            pivot = pivot.parent
        }
        pivot as Base<*>
        indices.add(0, pivot.index.raw)
        val basePointer = pivot.basePointer

        return Triple(basePointer, indices, pointeeType)
    }

    private class Base<P : LlvmType>(
        val basePointer: LlvmValue<LlvmPointerType<out P>>,
        val index: LlvmValue<LlvmIntegerType>,
    ) : GetElementPointerStep<P>(basePointer.type.pointed)
    private class Subsequent<P : LlvmType>(
        val parent: GetElementPointerStep<*>,
        val index: LlvmValue<LlvmIntegerType>,
        pointeeType: P,
    ) : GetElementPointerStep<P>(pointeeType)

    companion object {
        fun <P : LlvmType> initial(basePointer: LlvmValue<LlvmPointerType<out P>>, index: LlvmValue<LlvmIntegerType>): GetElementPointerStep<P> {
            return Base(basePointer, index)
        }

        fun <S : LlvmStructType, MemberType : LlvmType> GetElementPointerStep<S>.member(
            memberProp: KProperty1<S, LlvmStructType.Member<MemberType>>
        ): GetElementPointerStep<MemberType> {
            val member = memberProp(pointeeType)
            return step(
                member.type.context.i32(member.indexInStruct),
                member.type
            )
        }
    }
}