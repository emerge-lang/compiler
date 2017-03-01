import compiler.ast.context.SoftwareContext
import compiler.ast.type.BuiltinType
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
    // setup context
    val swCtx = SoftwareContext()
    swCtx.module("lang").context.include(BuiltinType.Context)

    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)

    println("------------")

    val matched = ModuleMatcher(arrayOf("testcode")).tryMatch(tokens.toTransactional())
    val parsedModule = matched.result

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach { println(it); println(); println() }

    // --
    if (parsedModule != null) {
        parsedModule.attachTo(swCtx)

        // TODO: validate context
    }
}