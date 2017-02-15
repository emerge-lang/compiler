import lexer.*
import parser.toTransactional

val testCode = """import package.*

"""

fun main(args: Array<String>) {
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)

    println("------------")

    val matched = Import.tryMatch(tokens.toTransactional())

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    for (error in matched.errors) {
        println(error)
    }

    println()

    println(matched)
}