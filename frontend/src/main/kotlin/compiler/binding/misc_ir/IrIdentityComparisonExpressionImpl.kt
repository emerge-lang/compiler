package compiler.binding.misc_ir

import compiler.binding.context.SoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrIdentityComparisonExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class IrIdentityComparisonExpressionImpl private constructor(
    override val lhs: IrTemporaryValueReference,
    override val rhs: IrTemporaryValueReference,
    private val getEvaluatesTo: () -> IrType,
) : IrIdentityComparisonExpression {
    constructor(lhs: IrTemporaryValueReference, rhs: IrTemporaryValueReference, ctx: SoftwareContext) : this(
        lhs,
        rhs,
        { ctx.bool.baseReference.toBackendIr() },
    )

    override val evaluatesTo = getEvaluatesTo()
}