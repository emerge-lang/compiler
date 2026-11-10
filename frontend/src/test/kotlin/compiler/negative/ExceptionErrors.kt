package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.diagnostic.ConstructorCouldBeNothrowDiagnostic
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
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
                .shouldFind<FunctionMissingAttributeDiagnostic> {
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
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
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
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "as the argument of a nothrow invocation" {
                validateModule("""
                    intrinsic fn dangerous() -> S32
                    nothrow fn id(x: S32) -> S32 = x
                    nothrow fn safe() -> S32 = id(dangerous())
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "as the receiver of a nothrow invocation" {
                validateModule("""
                    class Holder {
                        export nothrow fn value(self) -> S32 = 1
                    }
                    intrinsic fn dangerous() -> Holder
                    nothrow fn safe() -> S32 = dangerous().value()
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "as getter" {
                validateModule("""
                    class Foo {
                        get fn bla(self) = 1
                    }
                    
                    nothrow fn test(o: Foo) = o.bla
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "as setter" {
                validateModule("""
                    class Foo {
                        set fn bla(self: mut _, v: S32) {}
                    }
                    
                    nothrow fn test(o: mut Foo) {
                        set o.bla = 4
                    }
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }
        }

        "not-null assertion" - {
            "in function body" {
                validateModule("""
                    nothrow fn safe(p: Any?) -> Any = p!!
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.NotNullAssertion>()
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
                    .shouldFind<NothrowViolationDiagnostic.NotNullAssertion>()
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
                    .shouldFind<NothrowViolationDiagnostic.ThrowStatement>()
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
                    .shouldFind<NothrowViolationDiagnostic.ThrowStatement>()
            }
        }

        "constructors" - {
            "can be declared nothrow" {
                validateModule("""
                    class A {
                        nothrow constructor {}
                    }
                    nothrow fn test() -> A = A()
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "nothrow constructor cannot invoke throwing code" {
                validateModule("""
                    fn mayThrow() {}
                    class A {
                        nothrow constructor {
                            mayThrow()
                        }
                    }
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "member initializers of a nothrow constructor cannot throw" {
                validateModule("""
                    fn mayThrow() -> S32 = 1
                    class A {
                        x: S32 = mayThrow()
                        nothrow constructor {}
                    }
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "default constructor is nothrow" {
                validateModule("""
                    class A {
                        x: S32 = init
                    }
                    nothrow fn test() -> A = A(1)
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "member initializers of a default constructor cannot throw" {
                validateModule("""
                    fn mayThrow() -> S32 = 1
                    class A {
                        x: S32 = mayThrow()
                    }
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "explicit constructor without nothrow is throwing" {
                validateModule("""
                    fn mayThrow() {}
                    class A {
                        constructor {
                            mayThrow()
                        }
                    }
                    nothrow fn test() -> A = A()
                """.trimIndent())
                    .shouldFind<NothrowViolationDiagnostic.ThrowingInvocation>()
            }

            "explicit constructor without nothrow that can throw is fine" {
                validateModule("""
                    fn mayThrow() {}
                    class A {
                        constructor {
                            mayThrow()
                        }
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "explicit constructor without nothrow with throwing member initializer is fine" {
                validateModule("""
                    fn mayThrow() -> S32 = 1
                    class A {
                        x: S32 = mayThrow()
                        constructor {}
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "explicit constructor that could be nothrow gets a warning" {
                validateModule("""
                    class A {
                        constructor {}
                    }
                """.trimIndent())
                    .shouldFind<ConstructorCouldBeNothrowDiagnostic>()
            }

            "no suggestion to declare nothrow if the constructor has errors" {
                validateModule("""
                    class A {
                        constructor {
                            doesNotExist()
                        }
                    }
                """.trimIndent())
                    .shouldNotFind<ConstructorCouldBeNothrowDiagnostic>()
            }
        }
    }

    "throw statement" - {
        "value must be a subtype of throwable" {
            validateModule("""
                fn test() {
                    throw "Error"
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "const String"
                    it.targetType.toString() shouldBe "mut Throwable"
                }

            validateModule("""
                class SomeError : Throwable {}
                fn maybeException() -> Throwable? = SomeError() 
                fn test() {
                    throw maybeException()
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read Throwable?"
                    it.targetType.toString() shouldBe "mut Throwable"
                }
        }
    }
})
