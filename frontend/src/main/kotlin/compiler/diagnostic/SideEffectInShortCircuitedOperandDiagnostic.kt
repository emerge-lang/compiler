package compiler.diagnostic

import compiler.binding.impurity.Impurity
import compiler.lexer.Keyword
import compiler.lexer.Span

/**
 * The right-hand side of `and`/`or` is only evaluated depending on the left-hand side, so any side effect in it happens
 * only sometimes. `&` and `|` on [compiler.binding.context.SoftwareContext.bool] always evaluate both operands.
 */
class SideEffectInShortCircuitedOperandDiagnostic(
    val impurity: Impurity,
    val operator: Keyword,
) : Diagnostic(
    Severity.WARNING,
    "This operation has side effects, but it is only evaluated if the left-hand side of `${operator.text}` is ${if (operator == Keyword.AND) "true" else "false"}. " +
        "Use `${if (operator == Keyword.AND) "&" else "|"}` to always evaluate both sides.",
    impurity.span,
)

/**
 * Runs [action], passing all its findings on to `this`.
 * @return the [Impurity.span]s of all [SideEffectInShortCircuitedOperandDiagnostic]s reported by [action], so that
 * the impurity isn't reported a second time by an enclosing check.
 */
internal fun Diagnosis.reportingShortCircuitedSideEffects(action: (Diagnosis) -> Unit): Set<Span> {
    val spans = HashSet<Span>()
    Diagnosis.run {
        doWithTransformedFindings(action) { findings ->
            findings.onEach { finding ->
                if (finding is SideEffectInShortCircuitedOperandDiagnostic) {
                    spans.add(finding.impurity.span)
                }
            }
        }
    }
    return spans
}
