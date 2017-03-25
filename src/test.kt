import compiler.binding.context.SoftwareContext
import compiler.ast.type.BuiltinType
import compiler.lexer.*
import compiler.parser.grammar.CodeChunkRule
import compiler.parser.toTransactional

val testCode = """a.b!!()
"""

fun main(args: Array<String>) {
    // setup context
    val swCtx = SoftwareContext()
    swCtx.addModule(BuiltinType.Module)

    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    tokens.forEach(::println)

    println("------------")

    val matched = CodeChunkRule.INSTANCE.tryMatch(tokens.toTransactional(source.toLocation(1, 1)))
    // val parsedModule = matched.item
    // parsedModule?.context?.swCtx = swCtx

    println("certainty = ${matched.certainty}")
    println("item = ${matched.item}")

    println()
    println("Reportings:")
    println()

    matched.reportings.forEach { println(it); println(); println() }
}