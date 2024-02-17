package compiler.compiler.negative

import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.GlobalVariableNotInitializedReporting
import compiler.reportings.IllegalAssignmentReporting
import compiler.reportings.MultipleVariableDeclarationsReporting
import compiler.reportings.TypeDeductionErrorReporting
import compiler.reportings.UndefinedIdentifierReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.ValueNotAssignableReporting
import compiler.reportings.VariableAccessedBeforeInitializationReporting
import compiler.reportings.VariableDeclaredWithSplitTypeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class VariableErrors : FreeSpec({
    "toplevel" - {
        "Variable assignment type mismatch" {
            validateModule("""
                val foo: Int = false
            """.trimIndent())
                .shouldReport<ValueNotAssignableReporting> {
                    it.sourceType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.fullyQualifiedName.toString() shouldBe "emerge.core.Boolean"
                    it.targetType.shouldBeInstanceOf<RootResolvedTypeReference>().baseType.fullyQualifiedName.toString() shouldBe "emerge.core.Int"
                }
        }

        "variable type must be known" {
            validateModule("""
                val foo
            """.trimIndent())
                .shouldReport<TypeDeductionErrorReporting>()
        }

        "explicit modifier conflict" {
            validateModule("""
                mutable val foo: immutable Int
            """.trimIndent())
                .shouldReport<VariableDeclaredWithSplitTypeReporting>()
        }

        "unknown declared type" {
            validateModule("""
                val foo: Foo
            """.trimIndent())
                .shouldReport<UnknownTypeReporting>()
        }
    }

    "in function" - {
        "cannot assign to final variable" {
            validateModule("""
                fun foo() {
                    val a = 3
                    a = 5
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to a type" {
            validateModule("""
                fun foo() {
                    Int = 3
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to value" {
            validateModule("""
                fun foo() {
                    false  = 3
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "cannot assign to parameter" {
            validateModule("""
                fun foo(p: Int) {
                    p = 2
                }
            """.trimIndent())
                .shouldReport<IllegalAssignmentReporting>()
        }

        "variable declared multiple times" {
            validateModule("""
                fun foo() {
                    val x = 3
                    val a = 1
                    val x = true
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "x"
                    it.additionalDeclaration.name.value shouldBe "x"
                }
        }

        "accessing undeclared variable" {
            validateModule("""
                val x: Int = y
            """.trimIndent())
                .shouldReport<UndefinedIdentifierReporting>()
        }

        "unknown declared type" {
            validateModule("""
                fun test() {
                    val foo: Foo
                }
            """.trimIndent())
                .shouldReport<UnknownTypeReporting>()
        }

        "assignment status tracking" - {
            "global variable must be assigned at declaration" {
                validateModule("""
                    val a: Int
                """.trimIndent())
                    .shouldReport<GlobalVariableNotInitializedReporting>()
            }

            "local final variable can be assigned after declaration and then accessed" {
                validateModule("""
                    fun bar(p: Int) {
                    }
                    fun foo() {
                        val a: Int
                        bar(1)
                        a = 3
                        bar(a)
                    }
                """.trimIndent())
                    .shouldBeEmpty()
            }

            "local final variable cannot be accessed before initialization" {
                validateModule("""
                    fun bar(p: Int) {}
                    fun foo() {
                        val a: Int
                        bar(a)
                        a = 3
                    }
                """.trimIndent())
                    .shouldReport<VariableAccessedBeforeInitializationReporting>()
            }

            "local non-final variable can be assigned after declaration and then accessed, and reassigned" {
                validateModule("""
                    fun bar(p: Int) {
                    }
                    fun foo() {
                        var a: Int
                        bar(1)
                        a = 3
                        bar(a)
                        a = 4
                    }
                """.trimIndent())
                    .shouldBeEmpty()
            }

            "local non-final variable cannot be accessed before initialization" {
                validateModule("""
                    fun bar(p: Int) {}
                    fun foo() {
                        var a: Int
                        bar(a)
                        a = 3
                    }
                """.trimIndent())
                    .shouldReport<VariableAccessedBeforeInitializationReporting>()
            }
        }
    }

    "shadowing" - {
        "in function - forbidden" {
            validateModule("""
                fun foo() {
                    val a = 3
                    if true {
                        val a = 3
                    }
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing parameter" {
            validateModule("""
                fun foo(a: Int) {
                    val a = false
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - shadowing global" {
            validateModule("""
                val a = 3
                fun foo() {
                    val a = false
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }

        "in function - parameter shadowing global" {
            validateModule("""
                val a = 3
                fun foo(a: Boolean) {
                }
            """.trimIndent())
                .shouldReport<MultipleVariableDeclarationsReporting> {
                    it.originalDeclaration.name.value shouldBe "a"
                    it.additionalDeclaration.name.value shouldBe "a"
                }
        }
    }
})