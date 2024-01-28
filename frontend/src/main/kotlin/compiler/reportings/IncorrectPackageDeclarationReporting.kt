package compiler.reportings

import compiler.ast.ASTPackageName
import io.github.tmarsteel.emerge.backend.api.PackageName

class IncorrectPackageDeclarationReporting(
    val given: ASTPackageName,
    val expected: PackageName,
) : Reporting(
    Level.ERROR,
    "Incorrect package declaration. This file must be in package $expected",
    given.sourceLocation,
)