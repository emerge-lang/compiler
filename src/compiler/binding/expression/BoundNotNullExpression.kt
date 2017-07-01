package compiler.binding.expression

import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundNotNullExpression(
    override val context: CTContext,
    override val declaration: NotNullExpression,
    val nullableExpression: BoundExpression<*>
) : BoundExpression<NotNullExpression>, BoundExecutable<NotNullExpression> {
    // TODO: reporting on superfluous notnull when nullableExpression.type.nullable == false

    override var type: BaseTypeReference? = null
        private set

    override val isReadonly = true

    override fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()

    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()

    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()
}