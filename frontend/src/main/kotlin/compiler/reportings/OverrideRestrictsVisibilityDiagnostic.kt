package compiler.reportings

import compiler.binding.BoundFunction
import compiler.binding.BoundMemberFunction
import compiler.lexer.MemorySourceFile
import compiler.lexer.Span

data class OverrideRestrictsVisibilityDiagnostic(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Diagnostic(
    Level.ERROR,
    "The visibility of overrides must be the same or broader than that of the overridden function.",
    override.declaredAt,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(
            SourceHint(superFunction.visibilityLocation, "overridden function is ${superFunction.visibility}"),
            SourceHint(override.visibilityLocation, "override is ${override.visibility}"),
        )
        return str
    }
}

private val BoundFunction.visibilityLocation: Span
    get() = visibility.astNode.sourceLocation.takeUnless { it.sourceFile is MemorySourceFile && it.sourceFile.name == "UNKNOWN" }
        ?: declaredAt