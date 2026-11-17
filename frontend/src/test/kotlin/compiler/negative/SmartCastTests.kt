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
        fn takeMutBar(v: mut Bar) {}
        fn takeTwoBars(a: Bar, b: Bar) {}
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

    "a strict cast refines the variable in the code after it" - {
        "in the following statements" {
            validateModule("""
                $declarations
                fn test(v: Foo) -> String {
                    v as Bar
                    takeBar(v)
                    return v.p
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "in the following arguments" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    takeTwoBars(v as Bar, v)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "keeping the mutability of the variable" {
            validateModule("""
                $declarations
                fn test(v: mut Foo) {
                    v as Bar
                    takeMutBar(v)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not after a safe cast" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    v as? Bar
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not after a branch that may not have run" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if cond() {
                        v as Bar
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "inside the try block, but not after it, where the catch block may have run instead" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    try {
                        v as Bar
                        takeBar(v)
                    } catch e {
                    }
                    takeBar(v)
                }
            """.trimIndent())
                // exactly one: the one after the try
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not after a new value is assigned" {
            validateModule("""
                $declarations
                fn test() {
                    var w = produce()
                    w as Bar
                    set w = produce()
                    takeBar(w)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }
})
