package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.reportings.DroppingReferenceToObjectWithThrowingDestructorReporting
import compiler.reportings.FunctionMissingDeclaredModifierReporting
import compiler.reportings.NotNullAssertionInNothrowContextReporting
import compiler.reportings.ObjectMemberWithThrowingDestructorReporting
import compiler.reportings.ThrowingInvocationInNothrowContextReporting
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

    "nothrow violations - function body" - {

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
                .shouldReport<ThrowingInvocationInNothrowContextReporting>()
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
                .shouldReport<ThrowingInvocationInNothrowContextReporting>()
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
                .shouldReport<ThrowingInvocationInNothrowContextReporting>()
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
                .shouldReport<ThrowingInvocationInNothrowContextReporting>()
        }
    }

    "not-null assertion" - {
        "in function body" {
            validateModule("""
                nothrow fn safe(p: Any?) -> Any = p!!
            """.trimIndent())
                .shouldReport<NotNullAssertionInNothrowContextReporting>()
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
                .shouldReport<NotNullAssertionInNothrowContextReporting>()
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
                .shouldReport<NotNullAssertionInNothrowContextReporting>()
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
                .shouldReport<NotNullAssertionInNothrowContextReporting>()
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
                .shouldReport<DroppingReferenceToObjectWithThrowingDestructorReporting>()
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
                .shouldReport<ObjectMemberWithThrowingDestructorReporting>()
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
                .shouldReport<DroppingReferenceToObjectWithThrowingDestructorReporting>()
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
                .shouldReport<DroppingReferenceToObjectWithThrowingDestructorReporting>()
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
                .shouldReport<DroppingReferenceToObjectWithThrowingDestructorReporting>()
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
                .shouldReport<DroppingReferenceToObjectWithThrowingDestructorReporting>()
        }
    }
})