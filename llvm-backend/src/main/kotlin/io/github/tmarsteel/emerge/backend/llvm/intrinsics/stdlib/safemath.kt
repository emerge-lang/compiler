package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType

/**
 * first key: function name in the `emerge.core.safemath` package, e.g. `plusModulo`
 * second key: simple type name to operate on, e.g. `S8`
 */
val safemathFns: Map<String, Map<String, KotlinLlvmFunction<EmergeLlvmContext, *>>> = mapOf(
    "plusModulo" to mapOf(
        "S8" to buildModuloAdd("S8", LlvmI8Type),
        "U8" to buildModuloAdd("U8", LlvmI8Type),
        "S16" to buildModuloAdd("S16", LlvmI16Type),
        "U16" to buildModuloAdd("U16", LlvmI16Type),
        "S32" to buildModuloAdd("S32", LlvmI32Type),
        "U32" to buildModuloAdd("U32", LlvmI32Type),
        "S64" to buildModuloAdd("S64", LlvmI64Type),
        "U64" to buildModuloAdd("U64", LlvmI64Type),
        "SWord" to buildModuloAdd("SWord", EmergeWordType),
        "UWord" to buildModuloAdd("UWord", EmergeWordType),
    )
)

private fun <T : LlvmIntegerType> buildModuloAdd(
    typeSimpleName: String,
    llvmType: T,
) = KotlinLlvmFunction.define<EmergeLlvmContext, T>(
    "emerge.core.safemath.plusModulo_${typeSimpleName}",
    llvmType,
) {
    val lhs by param(llvmType)
    val rhs by param(llvmType)

    instructionAliasAttributes()

    body {
        ret(add(lhs, rhs))
    }
}