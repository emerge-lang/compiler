package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.reportings.ConstructorDeclaredNothrowReporting
import compiler.reportings.FunctionMissingDeclaredModifierReporting
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class ExceptionErrors : FreeSpec({
    "nothrow" - {
        "external implies nothrow" {
            validateModule("""
                external(C) fn test()
            """.trimIndent())
                .shouldReport<FunctionMissingDeclaredModifierReporting> {
                    it.attribute should beInstanceOf<AstFunctionAttribute.Nothrow>()
                }
        }

        "invoke throwing function" - {
            "in function body" {
                validateModule("""
                    intrinsic fn dangerous()
                    nothrow fn safe() {
                        dangerous()
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.ThrowingInvocation>()
            }

            "in destructor body" {
                validateModule("""
                    intrinsic fn dangerous()
                    class A {
                        nothrow destructor {
                            dangerous()
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.ThrowingInvocation>()
            }
        }

        "not-null assertion" - {
            "in function body" {
                validateModule("""
                    nothrow fn safe(p: Any?) -> Any = p!!
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.NotNullAssertion>()
            }

            "in destructor body" {
                validateModule("""
                    someV: Any? = 3
                    class A {
                        nothrow destructor {
                            someV!!
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.NotNullAssertion>()
            }
        }

        "throw statement" - {
            "in function body" {
                validateModule("""
                    class SomeError : Throwable {}
                    nothrow fn safe() {
                        throw SomeError()
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.ThrowStatement>()
            }

            "in destructor body" {
                validateModule("""
                    class SomeError : Throwable {}
                    class A {
                        nothrow destructor {
                            throw SomeError()
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationReporting.ThrowStatement>()
            }
        }

        "constructors cannot be nothrow" {
            validateModule("""
                class A {
                    nothrow constructor {}
                }
            """.trimIndent())
                .shouldReport<ConstructorDeclaredNothrowReporting>()
        }
    }

    "throw statement" - {
        "value must be a subtype of throwable" {
            validateModule("""
                fn test() {
                    throw "Error"
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "const String"
                    it.targetType.toString() shouldBe "read Throwable"
                }

            validateModule("""
                class SomeError : Throwable {}
                fn maybeException() -> Throwable? = SomeError() 
                fn test() {
                    throw maybeException()
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "read Throwable?"
                    it.targetType.toString() shouldBe "read Throwable"
                }
        }
    }
})
