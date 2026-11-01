package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute

context(builder: KotlinLlvmFunction.DefinitionReceiver<*, *>)
internal fun instructionAliasAttributes() {
    builder.functionAttribute(LlvmFunctionAttribute.AlwaysInline)
    builder.functionAttribute(LlvmFunctionAttribute.NoFree)
    builder.functionAttribute(LlvmFunctionAttribute.WillReturn)
    builder.functionAttribute(LlvmFunctionAttribute.NoRecurse)
    builder.functionAttribute(LlvmFunctionAttribute.NoUnwind)
}