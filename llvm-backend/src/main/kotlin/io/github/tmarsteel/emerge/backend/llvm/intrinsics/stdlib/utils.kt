package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute

context(KotlinLlvmFunction.DefinitionReceiver<*, *>)
internal fun instructionAliasAttributes() {
    functionAttribute(LlvmFunctionAttribute.AlwaysInline)
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
}