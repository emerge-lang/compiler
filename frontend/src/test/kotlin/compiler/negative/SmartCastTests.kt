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

    "isNull returning false refines the variable to non-null" - {
        "in the else branch" {
            validateModule("""
                $declarations
                fn test(v: Bar?) -> String {
                    if isNull(v) {
                        return "null"
                    } else {
                        takeBar(v)
                        return v.p
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "for value types" {
            validateModule("""
                $declarations
                fn test(v: S32?) -> S32 {
                    if isNull(v) {
                        return 0
                    } else {
                        return v + 1
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not in the then branch" {
            validateModule("""
                $declarations
                fn test(v: Bar?) {
                    if isNull(v) {
                        takeBar(v)
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not after the if" {
            validateModule("""
                $declarations
                fn test(v: Bar?) {
                    if isNull(v) {
                    } else {
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }

    "a safe cast evaluating to non-null refines the variable" - {
        "in the else branch of isNull" {
            validateModule("""
                $declarations
                fn test(v: Foo) -> String {
                    if isNull(v as? Bar) {
                        return "not a bar"
                    } else {
                        takeBar(v)
                        return v.p
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "also from a nullable type" {
            validateModule("""
                $declarations
                fn test(v: Foo?) {
                    if isNull(v as? Bar) {
                    } else {
                        takeBar(v)
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not in the then branch of isNull" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if isNull(v as? Bar) {
                        takeBar(v)
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }

    "after an if whose branch cannot complete normally, the implications of the other branch hold" - {
        "isNull with an early return" {
            validateModule("""
                $declarations
                fn test(v: Bar?) -> String {
                    if isNull(v) {
                        return "null"
                    }
                    takeBar(v)
                    return v.p
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "is-check with an else branch that returns" {
            validateModule("""
                $declarations
                fn test(v: Foo) {
                    if v is Bar {
                    } else {
                        return
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "inside a loop, for the same iteration" {
            validateModule("""
                $declarations
                fn test() {
                    var w: Bar? = Bar("x")
                    while cond() {
                        if isNull(w) {
                            return
                        }
                        takeBar(w)
                        set w = null
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not if the branch may complete normally" {
            validateModule("""
                $declarations
                fn test(v: Bar?) {
                    if isNull(v) {
                        if cond() {
                            return
                        }
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not if the other branch assigns a new value" {
            validateModule("""
                $declarations
                fn test() {
                    var w: Bar? = Bar("x")
                    if isNull(w) {
                        return
                    } else {
                        set w = null
                    }
                    takeBar(w)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not in a loop that can assign a new value on an earlier iteration" {
            validateModule("""
                $declarations
                fn test() {
                    var w: Bar? = Bar("x")
                    if isNull(w) {
                        return
                    }
                    while cond() {
                        takeBar(w)
                        set w = null
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        // break and continue leave a branch, too, and lead to the code after the loop
        "not if the branch may leave through a break, after returning otherwise" {
            validateModule("""
                $declarations
                fn test() {
                    var w: Bar? = Bar("x")
                    if isNull(w) {
                        return
                    }
                    while cond() {
                        if cond() {
                            if cond() {
                                set w = null
                                break
                            }
                            return
                        }
                    }
                    takeBar(w)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "not if the body of a loop may continue, after returning otherwise" {
            validateModule("""
                $declarations
                fn test() {
                    var w: Bar? = Bar("x")
                    if isNull(w) {
                        return
                    }
                    while cond() {
                        if cond() {
                            set w = null
                            continue
                        }
                        return
                    }
                    takeBar(w)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }

    "a not-null assertion refines the variable in the code after it" - {
        "in the following statements" {
            validateModule("""
                $declarations
                fn test(v: Bar?) -> String {
                    v!!
                    takeBar(v)
                    return v.p
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "in the following arguments" {
            validateModule("""
                $declarations
                fn test(v: Bar?) {
                    takeTwoBars(v!!, v)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not after a branch that may not have run" {
            validateModule("""
                $declarations
                fn test(v: Bar?) {
                    if cond() {
                        v!!
                    }
                    takeBar(v)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }
})
