package compiler.binding.misc_ir

import compiler.binding.context.SoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrIsNullExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class IrIsNullExpressionImpl private constructor(
    override val nullableValue: IrTemporaryValueReference,
    private val getEvaluatesTo: () -> IrType,
) : IrIsNullExpression {
    constructor(lhs: IrTemporaryValueReference, ctx: SoftwareContext) : this(
        lhs,
        { ctx.bool.irReadNotNullReference },
    )

    override val evaluatesTo = getEvaluatesTo()
}