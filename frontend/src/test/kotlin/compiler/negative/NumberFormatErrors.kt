package compiler.compiler.negative

import compiler.diagnostic.ErroneousLiteralExpressionDiagnostic
import io.kotest.core.spec.style.FreeSpec

class NumberFormatErrors : FreeSpec({
    "integer" - {
        "illegal char" {
            validateModule("""
                a: S32 = 3a
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }
    }

    "decimals" - {
        "illegal char without point" {
            validateModule("""
                a = 3pf
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char before point" {
            validateModule("""
                a = 3a.0
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char after point" {
            validateModule("""
                a = 3.0a
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }

        "empty exponent" {
            validateModule("""
                a = 3.4e
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }

        "illegal char in exponent" {
            validateModule("""
                a = 3.2e4gf
            """.trimIndent())
                .shouldFind<ErroneousLiteralExpressionDiagnostic>()
        }
    }
})