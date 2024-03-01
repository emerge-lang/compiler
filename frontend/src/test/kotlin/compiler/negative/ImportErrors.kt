package compiler.compiler.negative

import compiler.reportings.UnresolvableImportReporting
import compiler.reportings.UnresolvablePackageNameReporting
import io.kotest.core.spec.style.FreeSpec

class ImportErrors : FreeSpec({
    "unresolvable unused import" - {
        "unknown package" {
            validateModule("""
                import foo.bar.unused
                
                fun foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldReport<UnresolvablePackageNameReporting>()
        }

        "unknown symbol in known package" {
            validateModule("""
                import emerge.core.asdoghwegsdfas
                
                fun foo() -> String {
                    return "123"
                }
            """.trimIndent())
                .shouldReport<UnresolvableImportReporting>()
        }
    }
})