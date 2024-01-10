package compiler.compiler.negative

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.type.GenericTypeReference
import compiler.negative.shouldReport
import compiler.negative.validateModule
import compiler.reportings.MissingTypeArgumentReporting
import compiler.reportings.SuperfluousTypeArgumentsReporting
import compiler.reportings.TypeArgumentOutOfBoundsReporting
import compiler.reportings.TypeArgumentVarianceMismatchReporting
import compiler.reportings.TypeArgumentVarianceSuperfluousReporting
import compiler.reportings.UnsupportedTypeUsageVarianceReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class TypeErrors : FreeSpec({
    "generics" - {
        "assign to out-variant type parameter" {
            validateModule("""
                struct X<T> {
                    prop: T
                }
                
                fun foo() {
                    var myX: X<out Number> = X(2)
                    myX.prop = 2
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting>()
        }

        "assignment of generically typed value to directly typed variable" {
            validateModule("""
                fun foo<T>(p: T) {
                    val x: Any? = p
                }
            """.trimIndent())
                .shouldBeEmpty()
        }

        "assignment of directly typed value to generically typed variable" {
            validateModule("""
                fun foo<T>() {
                    val x: T = false
                }
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.simpleName shouldBe "Boolean"
                    it.targetType.shouldBeInstanceOf<GenericTypeReference>().simpleName shouldBe "T"
                }
        }

        "reference to generic type with arguments out of bounds" - {
            "unspecified variance" {
                validateModule("""
                    struct X<T : Number> {}
                    
                    val x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }

            "out variance" {
                validateModule("""
                    struct X<out T : Number> {}
                    
                    val x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }

            "in variance" {
                validateModule("""
                    struct X<in T : Number> {}
                    
                    val x: X<Any>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }
        }

        "reference to generic type with no type arguments when they are required" {
            validateModule("""
                struct X<T> {}
                val x: X
            """.trimIndent())
                .shouldReport<MissingTypeArgumentReporting> {
                    it.parameter.name.value shouldBe "T"
                }
        }

        "reference to generic type with too many type arguments when they are required" {
            validateModule("""
                struct X<T> {}
                val x: X<Int, Int, Boolean>
            """.trimIndent())
                .shouldReport<SuperfluousTypeArgumentsReporting> {
                    it.nExpected shouldBe 1
                    it.firstSuperfluousArgument.type.simpleName shouldBe "Int"
                }
        }

        "reference to generic type with mismatching parameter variance" {
            validateModule("""
                struct X<in T> {}
                val x: X<out Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceMismatchReporting>()

            validateModule("""
                struct X<out T> {}
                val x: X<in Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceMismatchReporting>()
        }

        "reference to generic type with superfluous parameter variance" {
            validateModule("""
                struct X<in T> {}
                val x: X<in Any>
            """.trimIndent())
                .shouldReport<TypeArgumentVarianceSuperfluousReporting>()
        }

        "reference to generic type with incompatible type argument mutability" - {
            "declaration-site" {
                validateModule("""
                    struct A<T : mutable Any> {
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
                    struct A<T : mutable Any> {
                        prop: T
                    }
                    val x = A(2)
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
                struct A<T> {
                    propOne: T
                    propTwo: T
                }
                val x: A<Int> = A(2, false)
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.toString() shouldBe "immutable Boolean"
                    it.targetType.toString() shouldBe "immutable Int"
                }
        }

        "use-site variance errors" - {
            "out type at struct member" {
                validateModule("""
                    struct X<out T> {
                        prop: T
                    }
                """.trimIndent())
                    .shouldReport<UnsupportedTypeUsageVarianceReporting>()
            }

            "in type at struct member" {
                validateModule("""
                    struct X<in T> {
                        prop: T
                    }
                """.trimIndent())
                    .shouldReport<UnsupportedTypeUsageVarianceReporting>()
            }
        }
    }
})