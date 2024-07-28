package compiler.binding

import compiler.ast.Statement
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop

interface BoundLoop<AstNode : Statement> : BoundStatement<AstNode> {
    override fun toBackendIrStatement(): IrLoop
}