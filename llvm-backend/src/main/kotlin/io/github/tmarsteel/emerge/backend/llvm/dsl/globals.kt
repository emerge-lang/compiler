package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

fun <S : LlvmStructType, C : LlvmContext> S.buildConstantIn(
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

    fun setNull(member: LlvmStructType.Member<S, *>) {
        valuesByIndex[member.indexInStruct] = context.nullValue(member.type)
    }

    internal fun build(): LLVMValueRef {
        (0  until structType.nMembers)
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

fun <E : LlvmType> LlvmArrayType<E>.buildConstantIn(
    context: LlvmContext,
    data: Iterable<LlvmValue<E>>,
): LlvmValue<LlvmArrayType<E>> {
    val constantsArray = data.map { it.raw }.toTypedArray()
    val constArray = LLVM.LLVMConstArray2(
        elementType.getRawInContext(context),
        PointerPointer(*constantsArray),
        constantsArray.size.toLong(),
    )

    return LlvmValue(constArray, this)
}