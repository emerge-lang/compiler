package compiler.compiler.negative

import compiler.reportings.AmbiguousFunctionReferenceReporting
import compiler.reportings.ReferencingUnknownTopLevelFunctionReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class FunctionReferenceErrors : FreeSpec({
    "toplevel" - {
        "referencing unknown function" {
            validateModule("""
                fn a(p: () -> Unit) {}
                fn test() {
                    a(::foobar)
                }
            """.trimIndent())
                .shouldReport<ReferencingUnknownTopLevelFunctionReporting> {
                    it.reference.nameToken.value shouldBe "foobar"
                }
        }

        "reference ambiguous" - {
            "with single overload set" {
                // this error should go away once overload resolution has been integrated into function references
                validateModule("""
                    intrinsic fn foobar(p: S32) -> Unit
                    intrinsic fn foobar(p: UWord) -> Unit
                    fn a(p: (S32) -> Unit) {}
                    fn test() {
                        a(::foobar)
                    }
                """.trimIndent())
                    .shouldReport<AmbiguousFunctionReferenceReporting>()
            }

            "ambiguous imports" {
                // this error should go away once overload resolution has been integrated into function references
                validateModules(
                    IntegrationTestModule.of("test.a", """
                        export fn foobar(p: S32) -> Unit
                    """.trimIndent()),
                    IntegrationTestModule.of("test.b", """
                        export fn foobar(p: UWord) -> Unit
                    """.trimIndent()),
                    IntegrationTestModule.of("testmodule", """
                        import test.a.foobar
                        import test.b.foobar
                        
                        fn a(p: (S32) -> Unit) {}
                        fn test() {
                            a(::foobar)
                        }
                    """.trimIndent())
                )
                        .shouldReport<AmbiguousFunctionReferenceReporting>()
            }

            "ambiguous parameter types" {
                // this error must not go away
                validateModule("""
                    intrinsic fn foobar(p: S32) -> Unit
                    intrinsic fn foobar(p: UWord) -> Unit
                    fn a(p: (Any) -> Unit) {}
                    fn test() {
                        a(::foobar)
                    }
                """.trimIndent())
                    .shouldReport<AmbiguousFunctionReferenceReporting>()
            }
        }
    }
})