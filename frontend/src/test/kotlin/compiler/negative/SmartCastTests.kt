package compiler.compiler.negative

import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec

/**
 * The backends trust the refined types of variables (they decide the representation of values), so the refinements
 * must be sound: they end where the variable can hold another value.
 */
class SmartCastTests : FreeSpec({
    val declarations = """
        interface Foo {}
        class Bar : Foo {
            p: String = init
        }
        fn takeBar(v: Bar) {}
        fn produce() -> Foo = Bar("x")
        fn cond() -> Bool = true
    """.trimIndent()

    "in the branch of an is-check, the variable has the refined type" - {
        "parameter" {
            validateModule("""
                $declarations
                fn test(v: Foo) -> String {
                    if v is Bar {
                        takeBar(v)
                        return v.p
                    }
                    return ""
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "re-assignable local variable" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    if w is Bar {
                        takeBar(w)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "global variable" {
            validateModule("""
                $declarations
                g: const Foo = Bar("x")
                fn test() {
                    if g is Bar {
                        takeBar(g)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "the refinement ends" - {
        "after the if" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if v is Bar {
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "in the else branch" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if v is Bar {
                    } else {
                        takeBar(v)
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "when a new value is assigned to the variable" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    if w is Bar {
                        set w = produce()
                        takeBar(w)
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "when a new value may have been assigned to the variable" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    if w is Bar {
                        if cond() {
                            set w = produce()
                        }
                        takeBar(w)
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "in a loop that can assign a new value to the variable on an earlier iteration" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    if w is Bar {
                        while cond() {
                            takeBar(w)
                            set w = produce()
                        }
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }

    "the refinement holds" - {
        "in a loop, for a variable that cannot be re-assigned" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if v is Bar {
                        while cond() {
                            takeBar(v)
                        }
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "when the is-check is inside the loop" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    while cond() {
                        if w is Bar {
                            takeBar(w)
                        }
                        set w = produce()
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "after an assignment in an unrelated branch" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    var other = produce()
                    if w is Bar {
                        if cond() {
                            set other = produce()
                        }
                        takeBar(w)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }
})
