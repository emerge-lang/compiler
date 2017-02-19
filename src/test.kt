import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """

readonly val a: Type = 3

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

    for (error in matched.errors) {
        println(error)
    }

    println()

    if (matched.isSuccess) {
        println(matched.result)
    }
}