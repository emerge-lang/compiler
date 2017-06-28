package compiler.binding.expression

import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression
) : BoundExpression<IdentifierExpression> {
    val identifier: String = declaration.identifier.value

    override var type: BaseTypeReference? = null
        private set

    /** What this expression refers to; is null if not known */
    var referredType: ReferredType? = null
        private set

    /** The variable this expression refers to, if it does (see [referredType]); otherwise null. */
    var referredVariable: BoundVariable? = null
        private set

    /**
     * Referring to things by their name is always readonly. Getters of variables must be readonly.
     */
    override val isReadonly = true

    override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // attempt a variable
        val variable = context.resolveVariable(identifier)
        if (variable != null) {
            type = variable.type
            referredVariable = variable
            referredType = ReferredType.VARIABLE
        }
        else {
            reportings.add(Reporting.error("Cannot resolve variable $identifier", declaration.sourceLocation))
        }

        // TODO: attempt to resolve type; expression becomes of type "Type/Class", ... whatever, still to be defined

        return reportings
    }

    /** The kinds of things an identifier can refer to. */
    enum class ReferredType {
        VARIABLE,
        TYPENAME
    }
}
