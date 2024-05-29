package compiler.compiler.binding

import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec

class InvocationRules : FreeSpec({
    // ignored for now because this requires a larger refactoring in BoundInvocationExpression, not in focus rn
    "given explicit generic types, parameters of generic types should induce their types into the arguments".config(enabled = false) {
        // explicitly specifying T = S8 must make the integer literal turn into an S8
        validateModule("""
            intrinsic fn inducer<T>(p: T)
            fn test() {
                inducer::<S8>(0)
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }
})