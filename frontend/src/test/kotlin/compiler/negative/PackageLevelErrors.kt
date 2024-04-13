package compiler.compiler.negative

import compiler.reportings.DuplicateBaseTypesReporting
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
            .shouldReport<DuplicateBaseTypesReporting> {
                it.duplicates should haveSize(3)
            }
    }
})