package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.expression.StringLiteralExpression
import compiler.ast.type.TypeMutability
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BuiltinType
import compiler.reportings.Reporting

class BoundStringLiteralExpression(
    override val context: CTContext,
    override val declaration: StringLiteralExpression,
) : BoundExpression<StringLiteralExpression> {
    override val isGuaranteedToThrow: Boolean = false
    override var type: BoundTypeReference? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val defaultModule = context.swCtx.module(*BuiltinType.DEFAULT_MODULE_NAME)
            ?: throw InternalCompilerError("Default module not present in the software context")
        val stringType = defaultModule.context.resolveBaseType("String")
            ?: throw InternalCompilerError("This software context doesn't define ${BuiltinType.DEFAULT_MODULE_NAME_STRING}.String")

        type = stringType.baseReference.withMutability(TypeMutability.IMMUTABLE)
        return emptySet()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do
    }
}