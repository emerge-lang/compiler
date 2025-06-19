package compiler.diagnostic

import compiler.ast.FunctionDeclaration

class NonVirtualMemberFunctionWithReceiverDiagnostic(
    decl: FunctionDeclaration,
    reason: String,
) : Diagnostic(
    Severity.ERROR,
    "This function declares a receiver that is not applicable for virtual functions: $reason. Declare this function outside of the type body.",
    decl.declaredAt,
)