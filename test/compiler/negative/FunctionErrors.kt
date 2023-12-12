package compiler.negative

import compiler.reportings.*
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class FunctionErrors : FreeSpec({
    "body" - {
        "external function cannot have body" {
            validateModule(
                """
                external fun foo() -> Int {
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
    }

    "modifier" - {
        "readonly+pure redundancy" {
            validateModule("""
            readonly pure fun foo() {}
        """.trimIndent())
                .shouldReport<ModifierInefficiencyReporting>()
        }

        "redundant modifiers readonly + pure" {
            validateModule("""
            readonly pure fun a() {}
        """.trimIndent())
                .shouldReport<ModifierInefficiencyReporting>()
        }
    }

    "return type mismatch" {
        validateModule("""
            fun a() -> Int {
                return true
            }
        """.trimIndent())
            .shouldReport<ReturnTypeMismatchReporting>()
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
            fun Foo.a() {
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "calling non-existent function overload" {
        validateModule("""
            fun foo(a: Int) {
            }
            
            fun test() {
                foo(true)
            }
        """.trimIndent())
            .shouldReport<UnresolvableFunctionOverloadReporting>()
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
    }
})