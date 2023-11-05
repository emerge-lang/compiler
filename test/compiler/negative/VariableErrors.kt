package matchers.compiler.negative

import compiler.reportings.IllegalAssignmentReporting
import compiler.reportings.ModifierErrorReporting
import compiler.reportings.TypeDeductionErrorReporting
import compiler.reportings.TypeMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.contain

class VariableErrors : FreeSpec({
    "toplevel" - {
        "Variable assignment type mismatch" {
            validateModule("""
                val foo: Int = false
            """.trimIndent())
                .shouldRejectWith<TypeMismatchReporting> {
                    it.sourceType.baseType.fullyQualifiedName shouldBe "dotlin.lang.Boolean"
                    it.targetType.baseType.fullyQualifiedName shouldBe "dotlin.lang.Int"
                }
        }

        "variable type must be known" {
            validateModule("""
                val foo
            """.trimIndent())
                .shouldRejectWith<TypeDeductionErrorReporting>()
        }

        "implicit modifier conflict" {
            validateModule("""
                val foo: mutable Int
            """.trimIndent())
                .shouldRejectWith<ModifierErrorReporting>()
        }

        "explicit modifier conflict" {
            validateModule("""
                mutable val foo: immutable Int
            """.trimIndent())
                .shouldRejectWith<ModifierErrorReporting>()
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
                .shouldRejectWith<IllegalAssignmentReporting>()
        }

        "cannot assign to a type" {
            validateModule("""
                fun foo() {
                    Int = 3
                }
            """.trimIndent())
                .shouldRejectWith<IllegalAssignmentReporting>()
        }

        "cannot assign to value" {
            validateModule("""
                fun foo() {
                    false  = 3
                }
            """.trimIndent())
                .shouldRejectWith<IllegalAssignmentReporting>()
        }
    }
})