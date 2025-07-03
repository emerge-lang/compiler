package compiler.util

import compiler.binding.BoundExecutable
import compiler.binding.context.DeferrableExecutable
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

fun <T> Iterable<T>.mapToBackendIrWithDebugLocations(
    span: T.() -> Span,
    ir: T.() -> IrExecutable,
): List<IrExecutable> {
    val iterator = iterator()
    if (!iterator.hasNext()) {
        return emptyList()
    }

    val firstStmt = iterator.next()
    var locationState = firstStmt.span()
    val size = if (this is Collection) size else 2
    val irList = ArrayList<IrExecutable>(size * 3 / 2)
    irList.add(IrUpdateSourceLocationStatementImpl(locationState))
    irList.add(firstStmt.ir())

    while (iterator.hasNext()) {
        val stmt = iterator.next()
        val stmtSpan = stmt.span()
        if (stmtSpan.lineNumber != locationState.lineNumber || stmtSpan.columnNumber != locationState.columnNumber) {
            locationState = stmtSpan
            irList.add(IrUpdateSourceLocationStatementImpl(locationState))
        }
        irList.add(stmt.ir())
    }

    return irList
}

fun Collection<BoundExecutable<*>>.mapToBackendIrWithDebugLocations() = mapToBackendIrWithDebugLocations(
    span = { declaration.span },
    ir = BoundExecutable<*>::toBackendIrStatement,
)

fun Sequence<DeferrableExecutable>.mapToBackendIrWithDebugLocations() = asIterable().mapToBackendIrWithDebugLocations(
    span = { span },
    ir = DeferrableExecutable::toBackendIrStatement,
)