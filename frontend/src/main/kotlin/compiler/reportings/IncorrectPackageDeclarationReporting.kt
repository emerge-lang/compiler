package compiler.reportings

import compiler.ast.ASTPackageName
import io.github.tmarsteel.emerge.backend.api.DotName

class IncorrectPackageDeclarationReporting(
    val given: ASTPackageName,
    val expected: DotName,
) : Reporting(
    Level.ERROR,
    "Incorrect package declaration. This file must be in package $expected",
    given.sourceLocation,
)