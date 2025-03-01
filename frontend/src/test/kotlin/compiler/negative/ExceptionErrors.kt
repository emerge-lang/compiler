package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.reportings.ConstructorDeclaredNothrowDiagnostic
import compiler.reportings.FunctionMissingDeclaredModifierDiagnostic
import compiler.reportings.NothrowViolationDiagnostic
import compiler.reportings.ValueNotAssignableDiagnostic
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
                .shouldReport<FunctionMissingDeclaredModifierDiagnostic> {
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
                    .shouldReport<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "in destructor body" {
                validateModule("""
                    intrinsic fn dangerous()
                    class A {
                        destructor {
                            dangerous()
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationDiagnostic.ThrowingInvocation>()
            }
        }

        "not-null assertion" - {
            "in function body" {
                validateModule("""
                    nothrow fn safe(p: Any?) -> Any = p!!
                """.trimIndent())
                    .shouldReport<NothrowViolationDiagnostic.NotNullAssertion>()
            }

            "in destructor body" {
                validateModule("""
                    someV: Any? = 3
                    class A {
                        destructor {
                            someV!!
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationDiagnostic.NotNullAssertion>()
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
                    .shouldReport<NothrowViolationDiagnostic.ThrowStatement>()
            }

            "in destructor body" {
                validateModule("""
                    class SomeError : Throwable {}
                    class A {
                        destructor {
                            throw SomeError()
                        }
                    }
                """.trimIndent())
                    .shouldReport<NothrowViolationDiagnostic.ThrowStatement>()
            }
        }

        "constructors cannot be nothrow" {
            validateModule("""
                class A {
                    nothrow constructor {}
                }
            """.trimIndent())
                .shouldReport<ConstructorDeclaredNothrowDiagnostic>()
        }
    }

    "throw statement" - {
        "value must be a subtype of throwable" {
            validateModule("""
                fn test() {
                    throw "Error"
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableDiagnostic> {
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
                .shouldReport<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read Throwable?"
                    it.targetType.toString() shouldBe "read Throwable"
                }
        }
    }
})
