package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.StandardLibraryModule
import compiler.ast.expression.StringLiteralExpression
import compiler.ast.type.TypeMutability
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundStringLiteralExpression(
    override val context: CTContext,
    override val declaration: StringLiteralExpression,
) : BoundExpression<StringLiteralExpression> {
    override val isGuaranteedToThrow: Boolean = false
    override var type: BoundTypeReference? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val defaultPackage = context.swCtx.getPackage(StandardLibraryModule.NAME)
            ?: throw InternalCompilerError("Standard Library module ${StandardLibraryModule.NAME} not present in software context")
        val stringType = defaultPackage.moduleContext.sourceFiles.asSequence()
            .map { it.context.resolveBaseType("String") }
            .filterNotNull()
            .firstOrNull()
            ?: throw InternalCompilerError("This software context doesn't define ${StandardLibraryModule.NAME}.String")

        type = stringType.baseReference.withMutability(TypeMutability.IMMUTABLE)
        return emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()
    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do
    }

    override fun toBackendIrExpression(): IrExpression = IrStringLiteralExpressionImpl(
        declaration.content.content.encodeToByteArray(),
        type!!.toBackendIr(),
    )
}

private class IrStringLiteralExpressionImpl(
    override val utf8Bytes: ByteArray,
    override val evaluatesTo: IrType
) : IrStringLiteralExpression