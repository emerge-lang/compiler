package matchers.compiler.negative

import compiler.reportings.*
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class VariableErrors : FreeSpec({
    "toplevel" - {
        "Variable assignment type mismatch" {
            validateModule("""
                val foo: Int = false
            """.trimIndent())
                .shouldReport<TypeMismatchReporting> {
                    it.sourceType.baseType.fullyQualifiedName shouldBe "dotlin.lang.Boolean"
                    it.targetType.baseType.fullyQualifiedName shouldBe "dotlin.lang.Int"
                }
        }

        "variable type must be known" {
            validateModule("""
                val foo
            """.trimIndent())
                .shouldReport<TypeDeductionErrorReporting>()
        }

        "implicit modifier conflict" {
            validateModule("""
                val foo: mutable Int
            """.trimIndent())
                .shouldReport<ModifierErrorReporting>()
        }

        "explicit modifier conflict" {
            validateModule("""
                mutable val foo: immutable Int
            """.trimIndent())
                .shouldReport<ModifierErrorReporting>()
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
    }
})