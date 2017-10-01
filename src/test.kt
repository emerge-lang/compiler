import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.Reporting

import compiler.parser.toTransactional

val testCode = """module testcode

fun a() -> Int {
    if true {
        return 1
    }
    else
    {
        return 2
    }
}

fun b() -> Int {
    return if true 1.2 else 2
}

fun c() -> Int {
    return if (true) 1 else 2
}

"""

fun main(args: Array<String>) {
    // setup context
    val swCtx = SoftwareContext()
    val builtinsModule = BuiltinType.getNewModule()
    builtinsModule.context.swCtx = swCtx
    swCtx.addModule(builtinsModule)

    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = testCode.split("\n")
    }

    val tokens = lex(testCode, source)

    val matched = Module.tryMatch(tokens.toTransactional(source.toLocation(1, 1)))

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

    val parsedASTModule = matched.item!!

    swCtx.addModule(parsedASTModule.bindTo(swCtx))
    swCtx.doSemanticAnalysis().forEach { println(it); println(); println() }

    println("---")
}

val Iterable<Reporting>.containsErrors
    get() = map(Reporting::level).any { it.level >= Reporting.Level.ERROR.level }