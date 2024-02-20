package compiler.reportings

import compiler.ast.Expression
import compiler.binding.type.BaseType
import java.math.BigInteger

class IntegerLiteralOutOfRangeReporting(
    val literal: Expression,
    val expectedType: BaseType,
    val expectedRange: ClosedRange<BigInteger>,
) : Reporting(
    Level.ERROR,
    "An ${expectedType.simpleName} is expected here, but this literal is out of range. Must be in [${expectedRange.start}; ${expectedRange.endInclusive}]",
    literal.sourceLocation,
)