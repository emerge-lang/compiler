import compiler.ast.expression.NumericLiteralExpression
import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """

mutable val a: readonly Type = 321e

"""

fun main(args: Array<String>) {
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)

    println("------------")

    val matched = VariableDeclaration.tryMatch(tokens.toTransactional())

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach(::println)

    val litExp = matched.result!!.assignExpression as NumericLiteralExpression
    litExp.validate().forEach(::println)
}