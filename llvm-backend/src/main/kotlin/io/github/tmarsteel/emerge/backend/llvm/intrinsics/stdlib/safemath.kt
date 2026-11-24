package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.*
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeSWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType

/**
 * first key: function name in the `emerge.core.safemath` package, e.g. `plusModulo`
 * second key: simple type name to operate on, e.g. `S8`
 */
val safemathFns: Map<String, Map<String, KotlinLlvmFunction<EmergeLlvmContext, *>>> = mapOf(
    "plusModulo" to mapOf(
        "S8" to buildModuloAdd("S8", LlvmS8Type),
        "U8" to buildModuloAdd("U8", LlvmU8Type),
        "S16" to buildModuloAdd("S16", LlvmS16Type),
        "U16" to buildModuloAdd("U16", LlvmU16Type),
        "S32" to buildModuloAdd("S32", LlvmS32Type),
        "U32" to buildModuloAdd("U32", LlvmU32Type),
        "S64" to buildModuloAdd("S64", LlvmS64Type),
        "U64" to buildModuloAdd("U64", LlvmU64Type),
        "SWord" to buildModuloAdd("SWord", EmergeSWordType),
        "UWord" to buildModuloAdd("UWord", EmergeUWordType),
    ),
    "minusModulo" to mapOf(
        "S8" to buildModuloMinus("S8", LlvmS8Type),
        "U8" to buildModuloMinus("U8", LlvmU8Type),
        "S16" to buildModuloMinus("S16", LlvmS16Type),
        "U16" to buildModuloMinus("U16", LlvmU16Type),
        "S32" to buildModuloMinus("S32", LlvmS32Type),
        "U32" to buildModuloMinus("U32", LlvmU32Type),
        "S64" to buildModuloMinus("S64", LlvmS64Type),
        "U64" to buildModuloMinus("U64", LlvmU64Type),
        "SWord" to buildModuloMinus("SWord", EmergeSWordType),
        "UWord" to buildModuloMinus("UWord", EmergeUWordType),
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

private fun <T : LlvmIntegerType> buildModuloMinus(
    typeSimpleName: String,
    llvmType: T,
) = KotlinLlvmFunction.define<EmergeLlvmContext, T>(
    "emerge.core.safemath.minusModulo_${typeSimpleName}",
    llvmType,
) {
    val lhs by param(llvmType)
    val rhs by param(llvmType)

    instructionAliasAttributes()

    body {
        ret(sub(lhs, rhs))
    }
}