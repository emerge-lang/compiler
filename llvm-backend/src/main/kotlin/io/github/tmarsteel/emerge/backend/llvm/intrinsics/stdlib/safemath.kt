package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmU8Type
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