package compiler.negative

import compiler.reportings.ConditionNotBooleanReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.types.shouldBeInstanceOf

class ConditionTypeError : FreeSpec({
    "if" {
        val reportings = validateModule("""
            fun test() {
                if 3 {
                
                }
            }
        """.trimIndent())

        reportings should haveSize(1)
        reportings.forOne {
            it.shouldBeInstanceOf<ConditionNotBooleanReporting>()
        }
    }
})