package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.PointerToAnyEmergeValue
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.TypeinfoType

internal val anyReflect = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.reflection.reflectType",
    pointerTo(TypeinfoType.GENERIC),
) {
    val self by param(PointerToAnyEmergeValue)

    body {
        ret(
            self
                .anyValueBase()
                .member { typeinfo }
                .get()
                .dereference()
        )
    }
}