package compiler.compiler.negative

import compiler.negative.shouldReport
import compiler.negative.validateModule
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
    }
})

data class X<T>(var prop: T)
fun foo() {
    val myX: X<out Number> = X(2)
    //myX.prop = 2

}