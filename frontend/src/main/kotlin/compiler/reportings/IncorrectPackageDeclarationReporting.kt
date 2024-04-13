package compiler.reportings

import compiler.ast.AstPackageName
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

class IncorrectPackageDeclarationReporting(
    val given: AstPackageName,
    val expected: CanonicalElementName.Package,
) : Reporting(
    Level.ERROR,
    "Incorrect package declaration. This file must be in package $expected",
    given.sourceLocation,
)