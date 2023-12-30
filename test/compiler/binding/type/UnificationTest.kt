package compiler.compiler.binding.type

import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.BuiltinInt
import compiler.binding.type.RootResolvedTypeReference
import compiler.negative.shouldReport
import compiler.negative.validateModule
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class UnificationTest : FreeSpec({
    "Explicit type argument does not widen" {
        // assigning false for the parameter of the struct is okay since its bound is Any
        // but the type parameter explicitly states Int, so false is not acceptable
        // the point of this test is to make sure the compiler reports this as a problem with the
        // argument false rather than as a problem with the type arguments or parameters
        validateModule("""
            struct A<T> {
                prop: T
            }
            val x = A::<Int>(false)
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting> {
                it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinBoolean
                it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinInt
            }
    }
})