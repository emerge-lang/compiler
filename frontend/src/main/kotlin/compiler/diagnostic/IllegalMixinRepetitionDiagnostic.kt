package compiler.diagnostic

import compiler.InternalCompilerError
import compiler.ast.AstMixinStatement
import compiler.binding.context.ExecutionScopedCTContext

class IllegalMixinRepetitionDiagnostic(
    val mixinStatement: AstMixinStatement,
    val repetition: ExecutionScopedCTContext.Repetition,
) : Diagnostic(
    Severity.ERROR,
    run {
        val repetitionText = when (repetition) {
            ExecutionScopedCTContext.Repetition.MAYBE,
            ExecutionScopedCTContext.Repetition.ZERO_OR_MORE -> "might never be executed"
            ExecutionScopedCTContext.Repetition.ONCE_OR_MORE -> "may be executed multiple times"
            ExecutionScopedCTContext.Repetition.EXACTLY_ONCE -> throw InternalCompilerError("this is nonsensical; diagnostic on correct code")
        }

        "This mixin $repetitionText; mixins must always be executed exactly once per object construction"
    },
    mixinStatement.span,
)