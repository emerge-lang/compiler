package compiler.compiler.negative

import compiler.reportings.AmbiguousInvocationReporting
import compiler.reportings.ExplicitInferTypeNotAllowedReporting
import compiler.reportings.IllegalFunctionBodyReporting
import compiler.reportings.MissingFunctionBodyReporting
import compiler.reportings.MissingParameterTypeReporting
import compiler.reportings.MissingReturnValueReporting
import compiler.reportings.MultipleParameterDeclarationsReporting
import compiler.reportings.OverloadSetHasNoDisjointParameterReporting
import compiler.reportings.ReturnTypeMismatchReporting
import compiler.reportings.UncertainTerminationReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.UnresolvableFunctionOverloadReporting
import compiler.reportings.ValueNotAssignableReporting
import compiler.reportings.VarianceOnFunctionTypeParameterReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class FunctionErrors : FreeSpec({
    "body" - {
        "external function cannot have body" {
            validateModule(
                """
                external(C) fun foo() -> Int {
                    return 3
                }
            """.trimIndent()
            )
                .shouldReport<IllegalFunctionBodyReporting>()
        }

        "non-external function must have body" {
            validateModule(
                """
                fun foo() -> Int
            """.trimIndent()
            )
                .shouldReport<MissingFunctionBodyReporting>()
        }
    }

    "parameters" - {
        "function parameters must have explicit types" {
            validateModule(
                """
                fun foo(bar) = 3
            """.trimIndent()
            )
                .shouldReport<MissingParameterTypeReporting>() {
                    it.parameter.name.value shouldBe "bar"
                }
        }

        "parameter name duplicate" {
            validateModule("""
                fun foo(a: Int, a: Boolean, b: Int) {}
            """.trimIndent())
                    .shouldReport<MultipleParameterDeclarationsReporting> {
                        it.firstDeclaration.name.value shouldBe "a"
                        it.additionalDeclaration.name.value shouldBe "a"
                    }
        }

        "explicit type inference on parameters is not allowed" {
            validateModule("""
                fun foo(p: _) {}
            """.trimIndent())
                .shouldReport<ExplicitInferTypeNotAllowedReporting>()
        }
    }

    "unknown declared return type" {
        validateModule("""
            fun a() -> Foo {
                return 0
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "unknown declared receiver type" {
        validateModule("""
            fun a(self: Foo) {
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "overloads" - {
        "calling non-existent function overload" {
            // disabled because with the overload resolution algorithm not fleshed out completely
            // this test cannot run
            validateModule("""
                class A {}
                class B {}
                fun foo(p1: A) {}
                fun foo(p1: B) {}            
                fun test() {
                    foo(true)
                }
            """.trimIndent())
                    .shouldReport<UnresolvableFunctionOverloadReporting>()
        }

        "overload-set with single non-disjoint parameter is not valid" {
            validateModule("""
                fun foo(a: Number) {}
                fun foo(a: Int) {}
            """.trimIndent())
                .shouldReport<OverloadSetHasNoDisjointParameterReporting>()
        }

        "overload-set with multiple parameters, none of which has disjoint types, is not valid" {
            validateModule("""
                fun foo(a: Number, b: Any) {}
                fun foo(a: Any, b: Number) {}
            """.trimIndent())
                .shouldReport<OverloadSetHasNoDisjointParameterReporting>()
        }

        "overload set with multiple parameters, only one of which has disjoint types, is valid" {
            validateModule("""
                fun foo(a: Any, b: Any, c: Int, d: Any) {}
                fun foo(a: Int, b: String, c: String, d: Number) {}
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "ambiguous invocation involving valid overload sets" {
            validateModule("""
                fun println(p: Any) {}
                
                fun main() {
                    println("Hello, World!")
                }
            """.trimIndent())
                .shouldReport<AmbiguousInvocationReporting>()
        }

        "no argument assignable to a disjointly typed parameter" {
            validateModule("""
                class A {}
                class B {}
                fun foo(disjoint: A, p: Int) {}
                fun foo(disjoint: B, p: Int) {}
                fun test() {
                    foo(0, 0)
                }
            """.trimIndent())
                .shouldReport<UnresolvableFunctionOverloadReporting>()
        }

        "argument not assignable to non-disjointly typed parameter" {
            val (_, reportings) = validateModule("""
                class A {}
                class B {}
                fun foo(disjoint: A, p1: Int, p2: Int) {}
                fun foo(disjoint: B, p1: Int, p2: Int) {}
                fun test() {
                    foo(A(), "123", B())
                }
            """.trimIndent())

            reportings should haveSize(2)
            reportings.forOne {
                it.shouldBeInstanceOf<ValueNotAssignableReporting>().also {
                    it.sourceType.toString() shouldBe "immutable String"
                    it.targetType.toString() shouldBe "immutable Int"
                }
            }
            reportings.forOne {
                it.shouldBeInstanceOf<ValueNotAssignableReporting>().also {
                    it.sourceType.toString() shouldBe "immutable testmodule.B"
                    it.targetType.toString() shouldBe "immutable Int"
                }
            }
        }
    }

    "calling a function that doesn't exist by name" {
        validateModule("""
            fun test() {
                foo(true)
            }
        """.trimIndent())
            .shouldReport<UnresolvableFunctionOverloadReporting>()
    }

    "termination" - {
        "empty body in non-unit function" {
            validateModule("""
                fun a() -> Int {
                }
            """.trimIndent())
                .shouldReport<UncertainTerminationReporting>()
        }

        "return type mismatch" {
            validateModule("""
            fun a() -> Int {
                return true
            }
        """.trimIndent())
                .shouldReport<ReturnTypeMismatchReporting>()
        }

        "value-less return from" - {
            "from function that doesn't declare return type" {
                validateModule("""
                    fun a() {
                        return
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "from function that declares Unit return type" {
                validateModule("""
                    fun a() -> Unit {
                        return
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "from function that declares non-unit return type" {
                validateModule("""
                    fun a() -> Int {
                        return
                    }
                """.trimIndent())
                    .shouldReport<MissingReturnValueReporting>()
            }
        }

        "if where only then returns" {
            validateModule("""
                fun a(p: Boolean) -> Int {
                    if p {
                        return 0
                    } else {
                    }
                }
            """.trimIndent())
                .shouldReport<UncertainTerminationReporting>()
        }

        "if where only else returns" {
            validateModule("""
                fun a(p: Boolean) -> Int {
                    if p {
                    } else {
                        return 0
                    }
                }
            """.trimIndent())
                .shouldReport<UncertainTerminationReporting>()
        }

        // TODO: if where only one branch throws, one test for then and else each
        // TODO: loop where the termination (return + throw) is in the loop body and the condition is not always true
    }

    "generics" - {
        "unresolvable bound on type parameter" {
            validateModule("""
                fun foo<T : Bla>() {}
            """.trimIndent())
                .shouldReport<UnknownTypeReporting> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }

        "in variance on type parameter" {
            validateModule("""
                fun foo<in T : String>() {}
            """.trimIndent())
                .shouldReport<VarianceOnFunctionTypeParameterReporting> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "out variance on type parameter" {
            validateModule("""
                fun foo<out T : String>() {}
            """.trimIndent())
                .shouldReport<VarianceOnFunctionTypeParameterReporting> {
                    it.parameter.name.value shouldBe "T"
                }
        }
    }
})