
import compiler.ast.context.SoftwareContext
import compiler.ast.type.BuiltinType
import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """module testcode

pure fun x(x: Int) {
    val y =
    return x + y
}
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

    val matched = Module.tryMatch(tokens.toTransactional(source.toLocation(1, 1)))
    val parsedModule = matched.result
    parsedModule?.context?.swCtx = swCtx

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach { println(it); println(); println() }
}