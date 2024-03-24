package compiler.compiler.negative

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.type.GenericTypeReference
import compiler.reportings.MissingTypeArgumentReporting
import compiler.reportings.SuperfluousTypeArgumentsReporting
import compiler.reportings.TypeArgumentOutOfBoundsReporting
import compiler.reportings.TypeArgumentVarianceMismatchReporting
import compiler.reportings.TypeArgumentVarianceSuperfluousReporting
import compiler.reportings.UnsupportedTypeUsageVarianceReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class TypeErrors : FreeSpec({
    "generics" - {
        "assign to out-variant type parameter" {
            validateModule("""
                class X<T> {
                    prop: T
                }
                
                fun foo() {
                    var myX: X<out Number> = X(2)
                    set myX.prop = 2
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting>()
        }

        "assignment of generically typed value to directly typed variable" {
            validateModule("""
                fun foo<T>(p: T) {
                    x: Any? = p
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "assignment of directly typed value to generically typed variable" {
            validateModule("""
                fun foo<T>() {
                    x: T = false
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.simpleName shouldBe "Boolean"
                    it.targetType.shouldBeInstanceOf<GenericTypeReference>().simpleName shouldBe "T"
                }
        }

        "assignment to generically typed member variable" - {
            "matching types should pass" {
                validateModule("""
                    class Foo<T> {
                        var prop: T = init
                    }
                    fun test<T>(tInst1: T, tInst2: T) {
                        var v = Foo(tInst1)
                        set v.prop = tInst2
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "mismatch should error" {
                validateModule("""
                    class Foo<T> {
                        var x: T = init
                    }
                    fun test<T>(tInst1: T) {
                        var v = Foo(tInst1)
                        set v.x = false
                    }
                """.trimIndent())
                    .shouldReport<ValueNotAssignableReporting> {
                        it.sourceType.toString() shouldBe "immutable Boolean"
                        it.targetType.toString() shouldBe "T"
                    }
            }
        }

        "reference to generic type with arguments out of bounds" - {
            "unspecified variance" {
                validateModule("""
                    class X<T : Number> {}
                    
                    x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }

            "out variance" {
                validateModule("""
                    class X<out T : Number> {}
                    
                    x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }

            "in variance" {
                validateModule("""
                    class X<in T : Number> {}
                    
                    x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }
        }

        "reference to generic type with no type arguments when they are required" {
            validateModule("""
                class X<T> {}
                x: X
            """.trimIndent())
                .shouldReport<MissingTypeArgumentReporting> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "reference to generic type with too many type arguments when they are required" {
            validateModule("""
                class X<T> {}
                x: X<Int, Int, Boolean>
            """.trimIndent())
                .shouldReport<SuperfluousTypeArgumentsReporting> {
                    it.nExpected shouldBe 1
                    it.firstSuperfluousArgument.type.simpleName shouldBe "Int"
                }
        }

        "reference to generic type with mismatching parameter variance" {
            validateModule("""
                class X<in T> {}
                x: X<out Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceMismatchReporting>()

            validateModule("""
                class X<out T> {}
                x: X<in Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceMismatchReporting>()
        }

        "reference to generic type with superfluous parameter variance" {
            validateModule("""
                class X<in T> {}
                x: X<in Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceSuperfluousReporting>()
        }

        "reference to generic type with incompatible type argument mutability" - {
            "declaration-site" {
                validateModule("""
                    class A<T : mutable Any> {
                        prop: T
                    }
                    fun foo(p: A<immutable Int>) {}
                """.trimIndent())
                    .shouldReport<TypeArgumentOutOfBoundsReporting> {
                        it.argument.astNode.type shouldBe TypeReference("Int", TypeReference.Nullability.UNSPECIFIED, TypeMutability.IMMUTABLE)
                    }
            }

            "use-site" {
                validateModule("""
                    class A<T : mutable Any> {
                        prop: T = init
                    }
                    x = A(2)
                """.trimIndent())
                    .shouldReport<ValueNotAssignableReporting> {
                        it.sourceType.toString() shouldBe "immutable Int"
                        it.targetType.toString() shouldBe "mutable Any"
                        it.reason shouldBe "cannot assign a immutable value to a mutable reference"
                    }
            }
        }

        "generic validation involving multiple values of different types" {
            validateModule("""
                class A<T> {
                    propOne: T = init
                    propTwo: T = init
                }
                x: A<Int> = A(2, false)
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "immutable Any"
                    it.targetType.toString() shouldBe "immutable Int"
                }
        }

        "use-site variance errors" - {
            "out type at class member" {
                validateModule("""
                    class X<out T> {
                        prop: T = init
                    }
                """.trimIndent())
                    .shouldReport<UnsupportedTypeUsageVarianceReporting>()
            }

            "in type at class member" {
                validateModule("""
                    class X<in T> {
                        prop: T = init
                    }
                """.trimIndent())
                    .shouldReport<UnsupportedTypeUsageVarianceReporting>()
            }
        }
    }

    "array literal" - {
        "with no elements is Array<Any>" {
            validateModule("""
                x = []
                y: Array<String> = x
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "immutable Any"
                    it.targetType.toString() shouldBe "immutable String"
                }
        }

        "infers array type from elements" - {
            "all the same" {
                validateModule("""
                    x = [1, 2, 3]
                    y: Array<String> = x
                """.trimIndent())
                    .shouldReport<ValueNotAssignableReporting> {
                        it.sourceType.toString() shouldBe "immutable Int"
                        it.targetType.toString() shouldBe "immutable String"
                    }
            }

            "different types" {
                validateModule("""
                    x = [1, 1.2, 2, 2.5]
                    y: Array<String> = x
                """.trimIndent())
                    .shouldReport<ValueNotAssignableReporting> {
                        it.sourceType.toString() shouldBe "immutable Number"
                        it.targetType.toString() shouldBe "immutable String"
                    }
            }
        }

        "uses element type from expected return" {
            validateModule("""
                x: Array<Number> = [1, 2, 3, 4]
                y: Array<String> = x
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "immutable Number"
                    it.targetType.toString() shouldBe "immutable String"
                }
        }

        "validates expected return element type against elements" {
            validateModule("""
                x: Array<Int> = [1, 2, 3, "4"]
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "immutable String"
                    it.targetType.toString() shouldBe "immutable Int"
                }
        }
    }
})