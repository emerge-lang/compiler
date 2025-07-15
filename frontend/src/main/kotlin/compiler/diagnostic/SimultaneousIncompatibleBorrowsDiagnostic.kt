package compiler.diagnostic

import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeMutability
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

class SimultaneousIncompatibleBorrowsDiagnostic(
    variable: VariableDeclaration,
    val firstBorrowStartedAt: Span,
    val firstBorrowMutability: TypeMutability,
    val secondBorrowStartedAt: Span,
    val secondBorrowMutability: TypeMutability,
) : Diagnostic(
    Severity.ERROR,
    "Cannot borrow `${variable.name.value}` as ${secondBorrowMutability.keyword.text} here, because it is already borrowed as ${firstBorrowMutability.keyword.text}",
    secondBorrowStartedAt,
) {
    context(CellBuilder) override fun renderBody() {
        sourceHints(
            SourceHint(firstBorrowStartedAt, "borrowed as ${firstBorrowMutability.keyword.text} here", severity = Severity.INFO),
            SourceHint(secondBorrowStartedAt, "attempting to borrow as ${secondBorrowMutability.keyword.text} while a ${firstBorrowMutability.keyword.text} borrow is still active", severity = severity)
        )
    }
}