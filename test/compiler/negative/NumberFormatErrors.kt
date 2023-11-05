package matchers.compiler.negative

import compiler.reportings.ErroneousLiteralExpressionReporting
import io.kotest.core.spec.style.FreeSpec

class NumberFormatErrors : FreeSpec({
    "integer" - {
        "illegal char" {
            validateModule("""
                val a: Int = 3a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }
    }

    "decimals" - {
        "illegal char without point" {
            validateModule("""
                val a = 3pf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char before point" {
            validateModule("""
                val a = 3a.0
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char after point" {
            validateModule("""
                val a = 3.0a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "empty exponent" {
            validateModule("""
                val a = 3.4e
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char in exponent" {
            validateModule("""
                val a = 3.2e4gf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }
    }
})