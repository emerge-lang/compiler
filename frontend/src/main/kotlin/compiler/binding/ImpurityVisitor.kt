package compiler.binding

import compiler.diagnostic.Diagnosis
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.purityViolation

fun interface ImpurityVisitor {
    fun visit(impurity: PurityViolationDiagnostic.Impurity)
}

internal class DiagnosingImpurityVisitor(
    private val diagnosis: Diagnosis,
    private val boundaryForReporting: PurityViolationDiagnostic.SideEffectBoundary,
) : ImpurityVisitor {
    private val writesBeyondContext = HashSet<PurityViolationDiagnostic.Impurity>()
    private var firstReadSeen = false

    override fun visit(impurity: PurityViolationDiagnostic.Impurity) {
        when (impurity.kind) {
            PurityViolationDiagnostic.ActionKind.READ -> {
                firstReadSeen = true
                if (impurity !in writesBeyondContext) {
                    diagnosis.purityViolation(impurity, boundaryForReporting)
                }
            }
            PurityViolationDiagnostic.ActionKind.MODIFY -> {
                check(!firstReadSeen) {
                    "visit writes before reads for this class to work correctly!"
                }

                writesBeyondContext.add(impurity)
                diagnosis.purityViolation(impurity, boundaryForReporting)
            }
        }
    }
}