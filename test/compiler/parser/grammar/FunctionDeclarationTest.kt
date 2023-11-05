package matchers.compiler.parser.grammar

import compiler.ast.expression.NumericLiteralExpression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty
import compiler.parser.grammar.GrammarTestCase
import compiler.parser.grammar.StandaloneFunctionDeclaration
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class FunctionDeclarationTest : GrammarTestCase() { init {
    val result = tokenSequence {
        keyword(Keyword.READONLY)
        keyword(Keyword.NOTHROW)
        keyword(Keyword.FUNCTION)
        identifier("foo")
        operator(Operator.PARANT_OPEN)

        identifier("a")
        operator(Operator.COLON)
        identifier("Int")
        operator(Operator.COMMA)

        identifier("b")
        operator(Operator.COLON)
        identifier("Int")
        operator(Operator.ASSIGNMENT)
        numericLiteral("512")
        operator(Operator.COMMA)

        operator(Operator.PARANT_CLOSE)
        operator(Operator.RETURNS)
        identifier("Boolean")
        newline()
        operator(Operator.CBRACE_OPEN)
        newline()
        operator(Operator.CBRACE_CLOSE)
    }.matchAgainst(StandaloneFunctionDeclaration)

    result.certainty shouldBe ResultCertainty.DEFINITIVE
    result.item.shouldNotBeNull()
    result.item!!.declaredAt.sourceLine shouldBe "1"
    result.item!!.declaredAt.sourceColumn shouldBe "1"
    result.item!!.modifiers shouldBe setOf(FunctionModifier.READONLY, FunctionModifier.NOTHROW)
    result.item!!.parameters.parameters should haveSize(2)
    result.item!!.parameters.parameters.forOne {
        it.name shouldBe "a"
        it.type shouldBe TypeReference("Int", false)
    }
    result.item!!.parameters.parameters.forOne {
        it.name shouldBe "b"
        it.type shouldBe TypeReference("Int", false)
        it.initializerExpression.shouldBeInstanceOf<NumericLiteralExpression>().literalToken.stringContent shouldBe "512"
    }
    result.item!!.returnType shouldBe TypeReference("Boolean", false)
} }