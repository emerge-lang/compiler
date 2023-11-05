package matchers.compiler.negative

import compiler.reportings.ErroneousLiteralExpressionReporting
import io.kotest.core.spec.style.FreeSpec

class NumberFormatErrors : FreeSpec({
    "integer" - {
        "illegal char" {
            validateModule("""
                val a: Int = 3a
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }
    }

    "decimals" - {
        "illegal char without point" {
            validateModule("""
                val a = 3pf
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }

        "illegal char before point" {
            validateModule("""
                val a = 3a.0
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }

        "illegal char after point" {
            validateModule("""
                val a = 3.0a
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }

        "empty exponent" {
            validateModule("""
                val a = 3.4e
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }

        "illegal char in exponent" {
            validateModule("""
                val a = 3.2e4gf
            """.trimIndent())
                .shouldRejectWith<ErroneousLiteralExpressionReporting>()
        }
    }
})