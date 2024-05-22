package compiler.binding.misc_ir

import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrUpdateSourceLocationStatement

internal class IrUpdateSourceLocationStatementImpl(
    span: Span
) : IrUpdateSourceLocationStatement {
    override val lineNumber = span.lineNumber
    override val columnNumber = span.columnNumber
}