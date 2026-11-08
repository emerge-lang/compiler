package compiler.compiler.parser

import compiler.ast.Expression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.ast.expression.AstIndexedLengthExpression
import compiler.ast.expression.AstRangeExpression
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.ast.expression.ParenthesisedExpression
import compiler.ast.expression.UnaryExpression
import compiler.compiler.negative.lexCode
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.nulls.shouldBeNull
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf
import compiler.parser.grammar.Expression as ExpressionRule

class ExpressionPrecedenceTest : FreeSpec({
    "grouping" - {
        listOf(
            "a-1" to "(a - 1)",
            "arr[$-1]" to "arr[($ - 1)]",
            "-x + 2" to "((- x) + 2)",
            "-x * 2 + 20" to "(((- x) * 2) + 20)",
            "x * -y" to "(x * (- y))",
            "a - -b" to "(a - (- b))",
            "--x" to "(- (- x))",
            "-1 + 2" to "(-1 + 2)",
            "-1.5" to "-1.5",
            "--1" to "(- -1)",
            "-(1)" to "(- (1))",
            "-x.foo()" to "(- x.foo())",
            "-1.toString()" to "(- 1.toString())",
            "not a and b" to "((not a) and b)",
            "not a == b" to "(not (a == b))",
            "not a == b and c" to "((not (a == b)) and c)",
            "a and not b" to "(a and (not b))",
            "not -x" to "(not (- x))",
            "a or b and c" to "(a or (b and c))",
            "a and b or c" to "((a and b) or c)",
            "a xor b and c" to "(a xor (b and c))",
            "a or b xor c" to "(a or (b xor c))",
            "a - b - c" to "((a - b) - c)",
            "a + b * c" to "(a + (b * c))",
            "a ?: b + c" to "(a ?: (b + c))",
            "0 ..< $-1" to "(0 ..< ($ - 1))",
        ).forEach { (code, expected) ->
            "$code -> $expected" {
                render(parseExpression(code)) shouldBe expected
            }
        }
    }

    "prefix operator weaker than its enclosing operator is marked" - {
        "after infix operator" {
            val expr = parseExpression("a == not b").shouldBeInstanceOf<BinaryExpression>()
            val notExpr = expr.rightHandSide.shouldBeInstanceOf<UnaryExpression>()
            notExpr.weakerThanEnclosingOperator.shouldNotBeNull().name shouldBe "=="
        }

        "after prefix operator" {
            val expr = parseExpression("- not x").shouldBeInstanceOf<UnaryExpression>()
            expr.weakerThanEnclosingOperator.shouldBeNull()
            val notExpr = expr.valueExpression.shouldBeInstanceOf<UnaryExpression>()
            notExpr.weakerThanEnclosingOperator.shouldNotBeNull().name shouldBe "-"
        }

        "not marked when parenthesised" {
            val expr = parseExpression("a == (not b)").shouldBeInstanceOf<BinaryExpression>()
            val notExpr = expr.rightHandSide.shouldBeInstanceOf<ParenthesisedExpression>().nested.shouldBeInstanceOf<UnaryExpression>()
            notExpr.weakerThanEnclosingOperator.shouldBeNull()
        }
    }
})

private val CompleteExpression = sequence {
    ref(ExpressionRule)
    endOfInput()
}
    .astTransformation { it.next() as Expression }

private fun parseExpression(code: String): Expression {
    val result = matchAgainst(lexCode(code, addPackageDeclaration = false), CompleteExpression)
    return result.shouldBeInstanceOf<MatchingResult.Success<Expression>>().item
}

private fun render(expr: Expression): String = when (expr) {
    is BinaryExpression -> "(${render(expr.leftHandSide)} ${expr.operator.name.lowercase()} ${render(expr.rightHandSide)})"
    is AstRangeExpression -> "(${render(expr.start)} ${expr.operator.name} ${render(expr.endExclusive)})"
    is UnaryExpression -> "(${expr.operator.name.lowercase()} ${render(expr.valueExpression)})"
    is NumericLiteralExpression -> (if (expr.minusToken != null) "-" else "") + expr.literalToken.stringContent
    is IdentifierExpression -> expr.identifier.value
    is ParenthesisedExpression -> "(${render(expr.nested)})"
    is MemberAccessExpression -> "${render(expr.valueExpression)}.${expr.memberName.value}"
    is InvocationExpression -> "${render(expr.targetExpression)}(${expr.argumentExpressions.joinToString(transform = ::render)})"
    is AstIndexAccessExpression -> "${render(expr.valueExpression)}[${render(expr.indexExpression)}]"
    is AstIndexedLengthExpression -> "$"
    else -> error("cannot render $expr")
}
