import compiler.ast.context.SoftwareContext
import compiler.ast.type.BuiltinType
import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """
module testcode

pure fun x() {
    val a: Any = 3
    return 3
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

    val matched = Module.tryMatch(tokens.toTransactional())
    val parsedModule = matched.result
    parsedModule?.context?.swCtx = swCtx

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach { println(it); println(); println() }

    parsedModule!!.context.resolveDefinedFunctions("x").first().declaration.code!!.validate(parsedModule.context)
        .forEach { println(it); println(); println() }
}