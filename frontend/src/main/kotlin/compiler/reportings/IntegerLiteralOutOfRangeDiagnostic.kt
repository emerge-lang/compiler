package compiler.reportings

import compiler.ast.Expression
import compiler.binding.basetype.BoundBaseType
import java.math.BigInteger

class IntegerLiteralOutOfRangeDiagnostic(
    val literal: Expression,
    val expectedType: BoundBaseType,
    val expectedRange: ClosedRange<BigInteger>,
) : Diagnostic(
    Level.ERROR,
    "An ${expectedType.simpleName} is expected here, but this literal is out of range. Must be in [${expectedRange.start}; ${expectedRange.endInclusive}]",
    literal.span,
)