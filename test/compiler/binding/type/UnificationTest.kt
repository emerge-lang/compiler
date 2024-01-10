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
    "Explicit type argument does not widen" - {
        // assigning false for the parameter of the struct is okay since its bound is Any
        // but the type parameter explicitly states Int, so false is not acceptable
        // the point of this test is to make sure the compiler reports this as a problem with the
        // argument false rather than as a problem with the type arguments or parameters

        "invocation-declared type argument" {
            validateModule(
                """
                struct A<T> {
                    prop: T
                }
                val x = A::<Int>(false)
            """.trimIndent()
            )
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinBoolean
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinInt
                }
        }

        "expected-return-type-declared type argument" {
            validateModule(
                """
                struct A<T> {
                    prop: T
                }
                val x: A<Int> = A(false)
            """.trimIndent()
            )
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinBoolean
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe BuiltinInt
                }
        }
    }

    "Type variable isolation / name confusion" {
        /* TODO: define a recursive invocation that instantiates the type parameter for the invocation to something
           incompatible to the generic type T of the outer scope. The compiler must not confuse the two for each other,
           even though they are called T and both originate from the same source location of type parameter.
         */
        validateModule("""
            fun <T, E> foo(p1: T, p2: E): T {
                return foo(p2, p1)
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting> {
            }
    }
})