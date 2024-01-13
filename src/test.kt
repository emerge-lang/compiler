import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.ClasspathSourceFile
import compiler.lexer.lex
import compiler.parser.grammar.Module
import compiler.parser.grammar.rule.MatchingContext
import compiler.reportings.Reporting
import java.nio.file.Path
import java.time.Clock
import java.time.Duration

val testCode = """module testcode
var x: Array<Int>
val y: Boolean = x.size()
"""

fun main() {
    // setup context
    val measureClock = Clock.systemUTC()
    val startedAt = measureClock.instant()

    val swCtx = SoftwareContext()
    val builtinsModule = BuiltinType.getNewModule()
    builtinsModule.context.swCtx = swCtx
    swCtx.addModule(builtinsModule)

    val sourceFile = ClasspathSourceFile(Path.of("testcode"), testCode)
    val tokens = sourceFile.lex()

    val sourceInMemoryAt = measureClock.instant()
    println("Source in memory after ${Duration.between(startedAt, sourceInMemoryAt)}")

    val matched = Module.match(MatchingContext.None, tokens)
    val lexicalCompleteAt = measureClock.instant()
    println("Lexical analysis complete after ${Duration.between(startedAt, lexicalCompleteAt)}"
        + " (took ${Duration.between(sourceInMemoryAt, lexicalCompleteAt)})")

    println()
    println("Reportings:")
    println()

    matched.reportings.forEach { println(it); println(); println() }

    println("---")
    println()
    println()

    if (matched.reportings.containsErrors) {
        return
    }

    val parsedASTModule = matched.item!!

    swCtx.addModule(parsedASTModule.bindTo(swCtx))
    val semanticResults = swCtx.doSemanticAnalysis()
    val semanticCompleteAt = measureClock.instant()
    println("Semantic analysis complete after ${Duration.between(startedAt, semanticCompleteAt)}"
        + " (took ${Duration.between(lexicalCompleteAt, semanticCompleteAt)})")

    println()
    println("Reportings:")
    println()

    semanticResults.forEach { println(it); println(); println() }

    println("---")
}

val Iterable<Reporting>.containsErrors
    get() = map(Reporting::level).any { it.level >= Reporting.Level.ERROR.level }