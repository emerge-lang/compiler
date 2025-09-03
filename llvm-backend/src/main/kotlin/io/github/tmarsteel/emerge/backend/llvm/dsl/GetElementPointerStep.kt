package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef

sealed class GetElementPointerStep<P : LlvmType> private constructor(
    val pointeeType: P,
) {
    private var consumed = false

    private fun consume() {
        check(!consumed) {
            "This instance of ${this::class.simpleName} was not used with strict method-chaining."
        }
        consumed = true
    }

    fun <NewP : LlvmType> stepUnsafe(index: LlvmValue<LlvmIntegerType>, pointeeType: NewP): GetElementPointerStep<NewP> {
        consume()
        return Subsequent(this, index, pointeeType)
    }

    /**
     * @return first: the base pointer, second: the list of indices being traversed, third: the type the resulting pointer points to
     */
    internal fun completeAndGetData(): Triple<LlvmValue<LlvmPointerType<*>>, List<LlvmValueRef>, P> {
        consume()
        val indices = ArrayList<LlvmValueRef>()
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

        context(builder: BasicBlockBuilder<*, *>)
        fun <S : LlvmStructType, MemberType : LlvmType> GetElementPointerStep<S>.member(
            accessor: S.() -> LlvmStructType.Member<out S, MemberType>
        ): GetElementPointerStep<MemberType> {
            val member = accessor(pointeeType)
            return stepUnsafe(
                builder.context.s32(member.indexInStruct),
                member.type,
            )
        }

        fun <E : LlvmType> GetElementPointerStep<out LlvmArrayType<out E>>.index(
            index: LlvmValue<LlvmIntegerType>
        ): GetElementPointerStep<E> {
            return stepUnsafe(index, pointeeType.elementType)
        }
    }
}