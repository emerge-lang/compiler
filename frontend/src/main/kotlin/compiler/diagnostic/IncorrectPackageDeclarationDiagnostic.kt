package compiler.diagnostic

import compiler.ast.AstPackageName
import io.github.tmarsteel.emerge.common.CanonicalElementName

class IncorrectPackageDeclarationDiagnostic(
    val given: AstPackageName,
    val expected: CanonicalElementName.Package,
) : Diagnostic(
    Severity.ERROR,
    "Incorrect package declaration. This file must be in package $expected",
    given.span,
)