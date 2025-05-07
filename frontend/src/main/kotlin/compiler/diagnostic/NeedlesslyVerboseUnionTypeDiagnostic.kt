package compiler.diagnostic

import compiler.ast.type.TypeReference

class NeedlesslyVerboseUnionTypeDiagnostic(
    val supertype: TypeReference,
    val superfluousSubtype: TypeReference,
) : Diagnostic(
    Severity.WARNING,
    "This type is already part of the union, it can be elided.",
    superfluousSubtype.span!!
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(listOf(
        SourceHint(supertype.span!!, "This type includes (= is a supertype of) $superfluousSubtype"),
        SourceHint(superfluousSubtype.span!!, "this type is superfluous, elide it")
    ))}"
}