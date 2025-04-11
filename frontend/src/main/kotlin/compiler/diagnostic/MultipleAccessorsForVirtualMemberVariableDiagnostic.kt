package compiler.diagnostic

import compiler.ast.FunctionDeclaration

class MultipleAccessorsForVirtualMemberVariableDiagnostic(
    val accessorsOfSameKind: List<FunctionDeclaration>,
) : Diagnostic(
    Severity.ERROR,
    TODO(),
    TODO(),
)