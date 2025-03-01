package compiler.compiler.binding.type

import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.shouldReport
import compiler.compiler.negative.validateModule
import compiler.reportings.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class UnificationTest : FreeSpec({
    "Explicit type argument does not widen" - {
        // assigning false for the parameter of the class is okay since its bound is Any
        // but the type parameter explicitly states Int, so false is not acceptable
        // the point of this test is to make sure the compiler reports this as a problem with the
        // argument false rather than as a problem with the type arguments or parameters

        "invocation-declared type argument" {
            validateModule(
                """
                class A<T> {
                    prop: T = init
                }
                x = A::<S32>(false)
            """.trimIndent()
            )
                .shouldReport<ValueNotAssignableDiagnostic> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe bool
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType shouldBe s32
                }
        }

        "expected-return-type-declared type argument" {
            validateModule(
                """
                class A<T> {
                    prop: T = init
                }
                x: A<S32> = A(false)
            """.trimIndent()
            )
                .shouldReport<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const Any"
                    it.targetType.toString() shouldBe "const S32"
                }
        }
    }

    "Type variable isolation / name confusion" - {
        /*
        assumption after lots of thinking: with proper calls to ResolvedTypeReference.withVariables and
        contextualize in place in BoundInvocationExpression it seems to be impossible that at any point
        there are two instances of GenericTypeReference or TypeVariable originating from the same original
        BoundTypeParameter that are semantically different (and thus would need to be treated as two separate
        type variables).

        This test code offers plenty of chances for confusion if the type variables are not handled properly,
        so i assume it covers a useful set of potential bugs.
         */
        validateModule(
            """
                fn foo<T, E>(p1: T, p2: E) -> T {
                    x: E = foo(p2, p1)
                    return p1
                }
            """.trimIndent()
        )
            .shouldHaveNoDiagnostics()
    }

    "generic bound as supertype" - {
        "positive" {
            validateModule("""
                fn foo<A, B : A>(someA: A, someB: B) {
                    otherA: A = someB
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "negative A" {
            // as compared to the positive case, B does not have A as the bound, so the assignment becomes illegal
            validateModule("""
                fn foo<A, B>(someA: A, someB: B) {
                    otherA: A = someB
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableDiagnostic> {
                    it.sourceType.simpleName shouldBe "B"
                    it.targetType.simpleName shouldBe "A"
                }
        }

        "subtyping direction is correct" {
            // as compared to the positive case, the type hierarchy is flipped, also making the assignment illegal
            validateModule("""
                fn foo<A : B, B>(someA: A, someB: B) {
                    otherA: A = someB
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableDiagnostic> {
                    it.sourceType.simpleName shouldBe "B"
                    it.targetType.simpleName shouldBe "A"
                }
        }
    }
})