package io.github.tmarsteel.emerge.backend.llvm.dsl

internal class LlvmFunction<ReturnType : LlvmType> private constructor(
    val name: String,
    givenReturnType: ReturnType?,
    val bodyBuilder: (BodyBuilder.() -> LlvmValue<ReturnType>)?,
) {
    class BodyBuilder {

    }

    companion object {
        fun <ReturnType : LlvmType> declare(name: String, returnType: ReturnType) = LlvmFunction(name, returnType, null)
        fun <ReturnType : LlvmType> define(name: String, body: BodyBuilder.() -> LlvmValue<ReturnType>) = LlvmFunction(name, null, body)
    }
}