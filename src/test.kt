
import compiler.ast.context.MutableCTContext
import compiler.ast.context.SoftwareContext
import compiler.ast.type.BuiltinType
import compiler.lexer.*
import compiler.parser.toTransactional

val testCode = """
module testcode

val x: Int = 3 + 5

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
    // val matched = StandaloneFunctionDeclaration.tryMatch(tokens.toTransactional())
    // val parsedModule = matched.result

    println("certainty = ${matched.certainty}")
    println("result = ${matched.result}")

    println()
    println("Reportings:")
    println()

    matched.errors.forEach { println(it); println(); println() }

    val ctx = matched.result!!.context
    ctx.swCtx = swCtx
    println(
        ctx.resolveVariable("x")!!.declaration.assignExpression!!.determineType(ctx)
    )
}