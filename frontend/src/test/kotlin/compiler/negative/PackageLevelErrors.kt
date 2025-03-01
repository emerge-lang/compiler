package compiler.compiler.negative

import compiler.diagnostic.DuplicateBaseTypesDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should

class PackageLevelErrors : FreeSpec({
    "multiple types with same name" {
        validateModule("""
            interface Foo {}
            class Foo {}
            interface Foo {}
        """.trimIndent())
            .shouldReport<DuplicateBaseTypesDiagnostic> {
                it.duplicates should haveSize(3)
            }
    }
})