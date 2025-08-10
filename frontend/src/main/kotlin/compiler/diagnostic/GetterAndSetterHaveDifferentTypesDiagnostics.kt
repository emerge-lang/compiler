package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.diagnostic.rendering.CellBuilder

class GetterAndSetterHaveDifferentTypesDiagnostics(
    val getter: FunctionDeclaration,
    val setter: FunctionDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "The getter and setter for virtual member variable `${getter.name.value}` disagree on the type of the variable.",
    getter.declaredAt,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            val setterParam = setter.parameters.parameters.drop(1).firstOrNull()
            val setterSpan = setterParam?.type?.span ?: setterParam?.span ?: setter.declaredAt
            sourceHints(
                SourceHint(
                    getter.parsedReturnType?.span ?: getter.declaredAt,
                    "the getter returns one type",
                    relativeOrderMatters = false,
                    severity = severity
                ),
                SourceHint(
                    setterSpan,
                    "the setter takes another type",
                    relativeOrderMatters = false,
                    severity = severity
                ),
            )
        }
    }
}