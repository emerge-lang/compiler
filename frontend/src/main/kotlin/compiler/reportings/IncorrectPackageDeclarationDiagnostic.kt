package compiler.reportings

import compiler.ast.AstPackageName
import io.github.tmarsteel.emerge.common.CanonicalElementName

class IncorrectPackageDeclarationDiagnostic(
    val given: AstPackageName,
    val expected: CanonicalElementName.Package,
) : Diagnostic(
    Level.ERROR,
    "Incorrect package declaration. This file must be in package $expected",
    given.span,
)