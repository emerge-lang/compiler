package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.binding.BoundAssignmentStatement
import compiler.binding.DropLocalVariableStatement
import compiler.binding.expression.BoundInvocationExpression
import compiler.reportings.CallableMissingDeclaredModifierReporting
import compiler.reportings.ConstructorDeclaredNothrowReporting
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
                .shouldReport<CallableMissingDeclaredModifierReporting> {
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

            /**
             * [BoundInvocationExpression] also drops the temporaries for arguments, and other expressions that hide
             * an invocation consequently do, too (e.g. operators, array literals, ...). This is not a problem for nothrow,
             * Here goes the proof:
             *
             * before a call to another function, the refcount of all the arguments is at least 1. The drop-to-0 may happen
             * later, but not as a part of a [BoundInvocationExpression]; instead, this happens with [DropLocalVariableStatement].
             * And even then: if the function being called doesn't remove other heap references to any of its arguments,
             * there is no way for the refcounter to reach 0 after the invocation. If the called function was to remove heap
             * references for arguments that potentially throw on destruction, that function being called CANNOT BE nothrow:
             * To remove those references, it has to assign a new value to a heap reference. This requires refcounting the
             * previous value, also potentially triggering the destructor that thorws. In that case, that very
             * [BoundAssignmentStatement] would complain/raise a diagnostic.
             */
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
