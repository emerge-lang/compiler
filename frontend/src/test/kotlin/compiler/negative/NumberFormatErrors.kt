package compiler.compiler.negative

import compiler.reportings.ErroneousLiteralExpressionReporting
import io.kotest.core.spec.style.FreeSpec

class NumberFormatErrors : FreeSpec({
    "integer" - {
        "illegal char" {
            validateModule("""
                a: Int = 3a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }
    }

    "decimals" - {
        "illegal char without point" {
            validateModule("""
                a = 3pf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char before point" {
            validateModule("""
                a = 3a.0
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char after point" {
            validateModule("""
                a = 3.0a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "empty exponent" {
            validateModule("""
                a = 3.4e
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }

        "illegal char in exponent" {
            validateModule("""
                a = 3.2e4gf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionReporting>()
        }
    }
})