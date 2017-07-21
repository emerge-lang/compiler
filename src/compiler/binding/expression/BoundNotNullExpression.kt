package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.NotNullExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundNotNullExpression(
    override val context: CTContext,
    override val declaration: NotNullExpression,
    val nullableExpression: BoundExpression<*>
) : BoundExpression<NotNullExpression>, BoundExecutable<NotNullExpression> {
    // TODO: reporting on superfluous notnull when nullableExpression.type.nullable == false

    override var type: BaseTypeReference? = null
        private set

    override fun semanticAnalysisPhase1() = super<BoundExpression>.semanticAnalysisPhase1()
    override fun semanticAnalysisPhase2() = super<BoundExpression>.semanticAnalysisPhase2()
    override fun semanticAnalysisPhase3() = super<BoundExpression>.semanticAnalysisPhase3()

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return nullableExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet()
}