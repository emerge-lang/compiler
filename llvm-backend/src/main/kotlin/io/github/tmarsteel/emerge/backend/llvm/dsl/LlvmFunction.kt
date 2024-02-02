package io.github.tmarsteel.emerge.backend.llvm.dsl

import kotlin.reflect.KProperty
import kotlin.reflect.KProperty1
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.i32
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

internal class LlvmFunction<ReturnType : LlvmType> private constructor(
    val name: String,
    givenReturnType: ReturnType?,
    val bodyBuilder: (BasicBlockBuilder.() -> LlvmValue<ReturnType>)?,
) {
    class BasicBlockBuilder(
        private val context: LlvmContext
    ) : LlvmContext by context {
        private val builder = LLVM.LLVMCreateBuilderInContext(ref)

        fun <T : LlvmType> param(type: T) : ParameterDelegate<T> {
            TODO()
        }

        fun <BasePointee : LlvmType> getelementptr(
            base: LlvmValue<LlvmPointerType<out BasePointee>>,
            index: LlvmValue<LlvmIntegerType> = base.type.context.i32(0)
        ): GetElementPointerStep<BasePointee> {
            return GetElementPointerStep.initial(base, index)
        }

        fun <P : LlvmType> GetElementPointerStep<P>.get(): LlvmValue<LlvmPointerType<P>> {
            val (basePointer, indices, resultPointeeType) = completeAndGetData()
            val indicesRaw = PointerPointer(*indices.toTypedArray())
            val instruction = LLVM.LLVMBuildGEP2(builder, basePointer.type.raw, basePointer.raw, indicesRaw, indices.size, null) // TODO: name nullable?
            LLVM.LLVMInsertIntoBuilder(builder, instruction)
            return LlvmValue(instruction, LlvmPointerType(resultPointeeType))
        }

        fun <P : LlvmType> LlvmValue<LlvmPointerType<P>>.dereference(): LlvmValue<P> {
            val loadInstr = LLVM.LLVMBuildLoad2(builder, type.pointed.raw, raw, null as String?) // TODO: name nullable?
            LLVM.LLVMInsertIntoBuilder(builder, loadInstr)
            return LlvmValue(loadInstr, type.pointed)
        }

        fun <P : LlvmType> store(value: LlvmValue<P>, to: LlvmValue<LlvmPointerType<P>>) {
            val storeInstr = LLVM.LLVMBuildStore(builder, value.raw, to.raw)
            LLVM.LLVMInsertIntoBuilder(builder, storeInstr)
        }

        fun add(a: LlvmValue<LlvmIntegerType>, b: LlvmValue<LlvmIntegerType>): LlvmValue<LlvmIntegerType> {
            check(a.type.nBits == b.type.nBits)
            val addInstr = LLVM.LLVMBuildAdd(builder, a.raw, b.raw, null as String?)
            LLVM.LLVMInsertIntoBuilder(builder, addInstr)
            return LlvmValue(addInstr, a.type)
        }
    }

    class ParameterDelegate<T : LlvmType> {
        operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T> {
            TODO()
        }
    }

    companion object {
        fun <ReturnType : LlvmType> declare(name: String, returnType: ReturnType) = LlvmFunction(name, returnType, null)
        fun <ReturnType : LlvmType> define(name: String, body: BasicBlockBuilder.() -> LlvmValue<ReturnType>) = LlvmFunction(name, null, body)
    }
}

internal sealed class GetElementPointerStep<P : LlvmType> private constructor(
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