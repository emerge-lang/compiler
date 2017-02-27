import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """
module blub

import foo.bar
import bar.blub

mutable val a: readonly Type = 321e

val x = 3
val y = 4




val z = x + y

"""

fun main(args: Array<String>) {
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)

    println("------------")

    val moduleDeclaration = compiler.ast.ModuleDeclaration(
        source.toLocation(1, 1),
        arrayOf("testcode")
    )
    val matched = ModuleMatcher(moduleDeclaration).tryMatch(tokens.toTransactional())

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach { println(it); println(); println() }
}