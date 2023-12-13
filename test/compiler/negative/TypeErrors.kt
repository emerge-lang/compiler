package compiler.compiler.negative

import compiler.negative.shouldReport
import compiler.negative.validateModule
import compiler.reportings.TypeArgumentCountMismatchReporting
import compiler.reportings.TypeArgumentOutOfBoundsReporting
import compiler.reportings.TypeArgumentVarianceMismatchReporting
import compiler.reportings.TypeArgumentVarianceSuperfluousReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.core.spec.style.FreeSpec

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
                    
                    val x: X<Int>
                """.trimIndent())
                        .shouldReport<TypeArgumentOutOfBoundsReporting>()
            }
        }

        "reference to generic type with no type arguments when they are required" {
            validateModule("""
                struct X<T> {}
                val x: X
            """.trimIndent())
                .shouldReport<TypeArgumentCountMismatchReporting>()
        }

        "reference to generic type with too many type arguments when they are required" {
            validateModule("""
                struct X<T> {}
                val x: X<Int, Int, Boolean>
            """.trimIndent())
                .shouldReport<TypeArgumentCountMismatchReporting>()
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
    }

})
/*
class X<in T : Number>
fun foo() {
    val myX: X<Any>

}*/