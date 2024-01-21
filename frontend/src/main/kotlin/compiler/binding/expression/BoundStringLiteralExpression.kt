package compiler.binding.expression

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.ast.expression.StringLiteralExpression
import compiler.ast.type.TypeMutability
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting

class BoundStringLiteralExpression(
    override val context: CTContext,
    override val declaration: StringLiteralExpression,
) : BoundExpression<StringLiteralExpression> {
    override val isGuaranteedToThrow: Boolean = false
    override var type: BoundTypeReference? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val defaultPackage = context.swCtx.getPackage(CoreIntrinsicsModule.NAME)
            ?: throw InternalCompilerError("Default package not present in the software context")
        val stringType = defaultPackage.module.sourceFiles.asSequence()
            .map { it.context.resolveBaseType("String") }
            .filterNotNull()
            .firstOrNull()
            ?: throw InternalCompilerError("This software context doesn't define ${CoreIntrinsicsModule.NAME_STRING}.String")

        type = stringType.baseReference.withMutability(TypeMutability.IMMUTABLE)
        return emptySet()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do
    }
}