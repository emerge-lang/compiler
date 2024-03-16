package compiler.compiler.negative

import compiler.reportings.ClassMemberVariableNotInitializedReporting
import compiler.reportings.DuplicateClassMemberReporting
import compiler.reportings.ImpureInvocationInPureContextReporting
import compiler.reportings.ReadInPureContextReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class ClassErrors : FreeSpec({
    "duplicate member" {
        validateModule("""
            class X {
                a: Int
                b: Int
                a: Boolean
            }
        """.trimIndent())
            .shouldReport<DuplicateClassMemberReporting> {
                it.duplicates should haveSize(2)
                it.duplicates.forAll {
                    it.name shouldBe "a"
                }
            }
    }

    "unknown declared member type" {
        validateModule("""
            class X {
                a: Foo
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "calling a constructor with incorrect argument types" {
        validateModule("""
            class X {
                a: Int = true
            }
            
            fun foo() {
                x = X(true)
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting>()
    }

    "calling a hypothetical constructor of a non-existent type" {
        validateModule("""
            x = Nonexistent()
        """.trimIndent())
    }

    "member variables" - {
        "class member variables must be initialized" {
            validateModule("""
                class Foo {
                    x: Int
                }
            """.trimIndent())
                .shouldReport<ClassMemberVariableNotInitializedReporting>()
        }

        "class member variable initializers are pure" - {
            "cannot read" {
                validateModule("""
                    var x: Int = 3
                    class Foo {
                        y: Int = x
                    }
                """.trimIndent())
                    .shouldReport<ReadInPureContextReporting>()
            }

            "cannot call readonly functions" {
                validateModule("""
                    intrinsic readonly fun bar() -> Int
                    class Foo {
                        x: Int = bar()
                    }
                """.trimIndent())
                    .shouldReport<ImpureInvocationInPureContextReporting>()
            }

            // TODO: as soon as there are lambdas, add a test to verify a run { ... } initializer can't write
        }
    }

    "generics" - {
        "type parameter with unresolvable bound" {
            validateModule("""
                class X<T : Bla> {}
            """.trimIndent())
                .shouldReport<UnknownTypeReporting> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }
    }
})