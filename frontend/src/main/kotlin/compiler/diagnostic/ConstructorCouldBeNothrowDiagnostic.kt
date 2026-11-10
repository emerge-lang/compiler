package compiler.diagnostic

import compiler.binding.basetype.BoundClassConstructor
import compiler.lexer.Keyword

class ConstructorCouldBeNothrowDiagnostic(
    val constructor: BoundClassConstructor,
) : Diagnostic(
    Severity.WARNING,
    "This constructor is effectively ${Keyword.NOTHROW.text}, consider declaring it as such.",
    constructor.declaredAt,
)
