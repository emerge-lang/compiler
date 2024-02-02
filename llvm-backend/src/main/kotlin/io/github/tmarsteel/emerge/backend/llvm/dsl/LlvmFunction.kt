package io.github.tmarsteel.emerge.backend.llvm.dsl

import kotlin.reflect.KProperty

internal class LlvmFunction<ReturnType : LlvmType> private constructor(
    val name: String,
    givenReturnType: ReturnType?,
    val bodyBuilder: (BodyBuilder.() -> LlvmValue<ReturnType>)?,
) {
    class BodyBuilder {
        val context: LlvmContext get() = TODO()

        fun <T : LlvmType> param(type: T) : ParameterDelegate<T> {
            TODO()
        }

        fun getelementptr<BasePointee : LlvmType>(base: LlvmValue<LlvmPointerType<BasePointee>>, index: Long) {
            TODO()
        }
    }

    class ParameterDelegate<T : LlvmType> {
        operator fun getValue(thisRef: Nothing?, prop: KProperty<*>): LlvmValue<T> {
            TODO()
        }
    }

    companion object {
        fun <ReturnType : LlvmType> declare(name: String, returnType: ReturnType) = LlvmFunction(name, returnType, null)
        fun <ReturnType : LlvmType> define(name: String, body: BodyBuilder.() -> LlvmValue<ReturnType>) = LlvmFunction(name, null, body)
    }
}