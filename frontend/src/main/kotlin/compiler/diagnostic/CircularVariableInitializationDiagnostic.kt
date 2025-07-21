package compiler.diagnostic

import compiler.ast.VariableDeclaration

class CircularVariableInitializationDiagnostic(
    val variable: VariableDeclaration,
) : Diagnostic(
    Severity.ERROR,
    "Initializing variable ${variable.name.quote()} requires that a value is already assigned to it;\nwhich effectively uses the variable before it is initialized.",
    variable.initializerExpression?.span ?: variable.declaredAt,
)