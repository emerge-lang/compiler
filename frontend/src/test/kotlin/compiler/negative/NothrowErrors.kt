package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.reportings.FunctionMissingDeclaredModifierReporting
import compiler.reportings.NothrowViolationReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.types.beInstanceOf

class NothrowErrors : FreeSpec({
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
            """.trimIndent()
            )
                .shouldReport<NothrowViolationReporting.ThrowingInvocation>()
        }

        "in constructor body" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    nothrow constructor {
                        dangerous()
                    }
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.ThrowingInvocation>()
        }

        "in class member initializer" {
            validateModule("""
                intrinsic fn dangerous() -> S32
                class A {
                    x: S32 = dangerous()
                    nothrow constructor {
                    }
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

        "in constructor body" {
            validateModule("""
                class A {
                    x: Any? = init
                    nothrow constructor {
                        self.x!!
                    }
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.NotNullAssertion>()
        }

        "in class member initializer" {
            validateModule("""
                someV: Any? = 3
                class A {
                    x: Any = someV!!
                    nothrow constructor {
                    }
                }
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

    "potentially dropping object with throwing destructor" - {
        "in function" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                nothrow fn test() {
                    v = A()
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.PotentialThrowingDestruction>()
        }

        "through class member" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                class B {
                    x: A = init
                    nothrow destructor {}
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.ObjectMemberWithThrowingDestructor>()
        }

        "unused function return value" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                nothrow fn createA() = A()
                nothrow fn test() {
                    createA()
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.PotentialThrowingDestruction>()
        }

        // TODO: BoundInvocationFunction (and in turn even ArrayLiteral) drop the argument temporaries
    }

    "assigning to a variable where dropping the previous value might throw" - {
        "in function body" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                var x: A? = A()
                nothrow mut fn safe() {
                    set x = null
                }
            """.trimIndent()
            )
                .shouldReport<NothrowViolationReporting.PotentialThrowingDestruction>()
        }

        "in constructor body" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                class B {
                    var x: A? = A()                                    
                    nothrow constructor {
                        set self.x = null
                    }
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.PotentialThrowingDestruction>()
        }

        "in destructor body" {
            validateModule("""
                intrinsic fn dangerous()
                class A {
                    destructor {
                        dangerous()
                    }
                }
                var x: A? = A()
                class B {
                    nothrow destructor {
                        set x = null
                    }
                }
            """.trimIndent())
                .shouldReport<NothrowViolationReporting.PotentialThrowingDestruction>()
        }
    }
})