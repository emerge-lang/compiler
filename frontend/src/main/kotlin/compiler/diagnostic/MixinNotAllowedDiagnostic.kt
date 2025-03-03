package compiler.diagnostic

import compiler.ast.AstMixinStatement

class MixinNotAllowedDiagnostic(
    val mixinStatement: AstMixinStatement,
) : Diagnostic(
    Severity.ERROR,
    "Mixins are only allowed in class constructors",
    mixinStatement.span,
)