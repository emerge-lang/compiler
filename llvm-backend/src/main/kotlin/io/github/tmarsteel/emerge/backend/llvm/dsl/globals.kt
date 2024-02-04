package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

fun <S : LlvmStructType, C : LlvmContext> S.insertConstantInto(
    context: C,
    data: ConstantStructBuilder<S, C>.() -> Unit,
): LlvmValue<S> {
    val builder = ConstantStructBuilder(this, context)
    builder.data()
    return LlvmValue(builder.build(), this)
}

class ConstantStructBuilder<S : LlvmStructType, C : LlvmContext>(
    private val structType: S,
    val context: C,
) {
    private val valuesByIndex = HashMap<Int, LlvmValue<*>>()

    fun <M : LlvmType> setValue(member: LlvmStructType.Member<S, M>, value: LlvmValue<M>) {
        valuesByIndex[member.indexInStruct] = value
    }

    internal fun build(): LLVMValueRef {
        (0 ..structType.nMembers)
            .find { index -> index !in valuesByIndex }
            ?.let {
                throw IllegalArgumentException("Missing data for struct member #$it")
            }

        val valuesArray = Array(structType.nMembers) {
            valuesByIndex[it]!!.raw
        }
        val valuesPointerPointer = PointerPointer(*valuesArray)

        return LLVM.LLVMConstStructInContext(context.ref, valuesPointerPointer, valuesArray.size, 0)
    }
}