package compiler.compiler.negative

import compiler.diagnostic.ErroneousLiteralExpressionDiagnostic
import io.kotest.core.spec.style.FreeSpec

class NumberFormatErrors : FreeSpec({
    "integer" - {
        "illegal char" {
            validateModule("""
                a: S32 = 3a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }
    }

    "decimals" - {
        "illegal char without point" {
            validateModule("""
                a = 3pf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char before point" {
            validateModule("""
                a = 3a.0
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char after point" {
            validateModule("""
                a = 3.0a
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }

        "empty exponent" {
            validateModule("""
                a = 3.4e
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char in exponent" {
            validateModule("""
                a = 3.2e4gf
            """.trimIndent())
                .shouldReport<ErroneousLiteralExpressionDiagnostic>()
        }
    }
})