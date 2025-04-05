package compiler.binding.impurity

import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.purityViolation
import compiler.lexer.Span

internal class DiagnosingImpurityVisitor(
    private val diagnosis: Diagnosis,
    private val boundaryForReporting: PurityViolationDiagnostic.SideEffectBoundary,
) : ImpurityVisitor {
    private val writesBeyondContext = HashSet<Span>()
    private var firstReadSeen = false

    override fun visit(impurity: Impurity) {
        when (impurity.kind) {
            Impurity.ActionKind.READ -> {
                firstReadSeen = true
                if (impurity.span !in writesBeyondContext) {
                    diagnosis.purityViolation(impurity, boundaryForReporting)
                }
            }
            Impurity.ActionKind.MODIFY -> {
                check(!firstReadSeen) {
                    "visit writes before reads for this class to work correctly!"
                }

                writesBeyondContext.add(impurity.span)
                diagnosis.purityViolation(impurity, boundaryForReporting)
            }
        }
    }
}