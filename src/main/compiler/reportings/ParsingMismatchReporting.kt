package compiler.reportings

import compiler.lexer.SourceLocation

class ParsingMismatchReporting(
    val expected: String,
    val actual: String,
    location: SourceLocation,
) : Reporting(Level.ERROR, "Unexpected $actual, expecting $expected", location)