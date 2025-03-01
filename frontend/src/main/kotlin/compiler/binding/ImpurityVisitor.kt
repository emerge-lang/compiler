package compiler.binding

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.modifyingPurityViolation
import compiler.diagnostic.readingPurityViolation

interface ImpurityVisitor {
    fun visitReadBeyondBoundary(purityBoundary: CTContext, read: BoundExpression<*>)
    fun visitWriteBeyondBoundary(purityBoundary: CTContext, write: BoundExecutable<*>)
}

internal class PurityViolationImpurityVisitor(
    private val reportTo: Diagnosis,
    private val boundaryForReporting: PurityViolationDiagnostic.SideEffectBoundary,
) : ImpurityVisitor {
    private val writesBeyondContext = HashSet<BoundExecutable<*>>()
    private var firstReadSeen = false
    override fun visitReadBeyondBoundary(purityBoundary: CTContext, read: BoundExpression<*>) {
        firstReadSeen = true
        if (read !in writesBeyondContext) {
            reportTo.readingPurityViolation(read, boundaryForReporting)
        }
    }

    override fun visitWriteBeyondBoundary(purityBoundary: CTContext, write: BoundExecutable<*>) {
        check(!firstReadSeen) {
            "visit writes before reads for this class to work correctly!"
        }

        writesBeyondContext.add(write)
        reportTo.modifyingPurityViolation(write, boundaryForReporting)
    }
}

internal class DetectingImpurityVisitor(
    private val lookFor: BoundExecutable<*>,
) : ImpurityVisitor {
    var foundAsReading: Boolean = false
        private set

    var foundAsWriting: Boolean = false
        private set

    override fun visitReadBeyondBoundary(purityBoundary: CTContext, read: BoundExpression<*>) {
        if (read == lookFor) {
            foundAsReading = true
        }
    }

    override fun visitWriteBeyondBoundary(purityBoundary: CTContext, write: BoundExecutable<*>) {
        if (write == lookFor) {
            foundAsWriting = true
        }
    }
}