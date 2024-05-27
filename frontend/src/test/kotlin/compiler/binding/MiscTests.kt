package compiler.compiler.binding

import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec

class MiscTests : FreeSpec({
    "member functions can recurse" {
        validateModule("""
            class Foo {
                fn a(self) {
                    self.a()
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "member functions can call other member functions of their owner type" {
        validateModule("""
            class Foo {
                fn a() {
                }
                fn b() {
                    Foo.a()
                }
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }
})