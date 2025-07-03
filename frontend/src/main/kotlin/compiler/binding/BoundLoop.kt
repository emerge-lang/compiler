package compiler.binding

import compiler.ast.Statement
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

interface BoundLoop<AstNode : Statement> : BoundStatement<AstNode> {
    /**
     * The loop node, same identity as the one that appears in [toBackendIrStatement]. Used by
     * [compiler.binding.expression.BoundBreakExpression] and [compiler.binding.expression.BoundContinueExpression]
     * to refer to the loop they are breaking/continuing.
     */
    val irLoopNode: IrLoop
}