import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.Reporting
import compiler.parser.toTransactional

val testCode = """module testcode

val foo: Int
val bar = 3
val foobar = foo2

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
    val parsedASTModule = matched.item!!

    println("certainty = ${matched.certainty}")
    println("item = ${matched.item}")

    println()
    println("Reportings:")
    println()

    matched.reportings.forEach { println(it); println(); println() }

    //
    if (matched.reportings.containsErrors) {
        return
    }

    swCtx.addModule(parsedASTModule.bindTo(swCtx))
    swCtx.doSemanticAnalysis().forEach { println(it); println(); println() }

    println("---")
}

val Iterable<Reporting>.containsErrors
    get() = map(Reporting::level).any { it.level > Reporting.Level.ERROR.level }