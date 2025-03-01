package compiler.compiler.negative

import compiler.diagnostic.UnresolvableImportDiagnostic
import compiler.diagnostic.UnresolvablePackageNameDiagnostic
import io.kotest.core.spec.style.FreeSpec

class ImportErrors : FreeSpec({
    "unresolvable unused import" - {
        "unknown package" {
            validateModule("""
                import foo.bar.unused
                
                fn foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldReport<UnresolvablePackageNameDiagnostic>()
        }

        "unknown symbol in known package" {
            validateModule("""
                import emerge.core.asdoghwegsdfas
                
                fn foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldReport<UnresolvableImportDiagnostic>()
        }
    }
})