package compiler.negative

import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.SourceDescriptor
import compiler.lexer.SourceLocation
import compiler.lexer.lex
import compiler.parser.TokenSequence
import compiler.parser.grammar.Module
import compiler.parser.grammar.rule.MatchingContext
import compiler.parser.toTransactional
import compiler.reportings.Reporting
import io.kotest.inspectors.forOne
import io.kotest.matchers.types.shouldBeInstanceOf
import java.math.MathContext

fun lexCode(code: String, addModuleDeclaration: Boolean = true): TokenSequence {
    return lexCodeInternal(code, addModuleDeclaration)
}

private fun getInvokedFromAsSourceLocation(additionalStackOffset: Int = 0): SourceLocation {
    val invokedFrom = Thread.currentThread().stackTrace[4 + additionalStackOffset]
    return SourceLocation(
        object : SourceDescriptor {
            override val sourceLocation = invokedFrom.fileName
        },
        invokedFrom.lineNumber,
        1,
    )
}

private fun lexCodeInternal(code: String, addModuleDeclaration: Boolean): TokenSequence {
    val initialSourceLocation = getInvokedFromAsSourceLocation(1)

    var moduleCode = code
    var nEmptyLinesToPrepend = initialSourceLocation.sourceLine
    if (addModuleDeclaration) {
        moduleCode = "module testmodule\n$code"
        nEmptyLinesToPrepend--
    }

    moduleCode = "\n".repeat(nEmptyLinesToPrepend.coerceAtLeast(0)) + moduleCode

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = initialSourceLocation.sD.sourceLocation
        override val sourceLines = moduleCode.split("\n")
    }
    val initialSourceLocationWithCode = SourceLocation(sourceDescriptor, initialSourceLocation.sourceLine, initialSourceLocation.sourceColumn)

    return lex(moduleCode, sourceDescriptor).toTransactional(initialSourceLocationWithCode)
}

/**
 * To be invoked with this exact syntax to have the line numbers match
 *
 * ```
 * VariableDeclaration.parseAndValidate("""
 *     // source line 1
 * """.trimMargin())
 * ```
 */
fun validateModule(code: String, addModuleDeclaration: Boolean = true): Collection<Reporting> {
    val tokens = lexCodeInternal(code.assureEndsWith('\n'), addModuleDeclaration)
    val result = Module.match(MatchingContext.None, tokens)
    if (result.item == null) {
        val error = result.reportings.maxBy { it.level }
        throw AssertionError("Failed to parse code: ${error.message} in ${error.sourceLocation}")
    }
    val lexicalReportings = result.reportings
    val nTopLevelDeclarations = result.item!!.let { module ->
        module.functions.size + module.structs.size + module.variables.size
    }
    check(nTopLevelDeclarations > 0) { "Found no top-level declarations in the test source. Very likely a parsing bug." }

    val swCtxt = SoftwareContext()

    swCtxt.addModule(result.item!!.bindTo(swCtxt))

    val builtinsModule = BuiltinType.getNewModule()
    builtinsModule.context.swCtx = swCtxt
    swCtxt.addModule(builtinsModule)

    val semanticReportings = swCtxt.doSemanticAnalysis()
    return (lexicalReportings + semanticReportings).toSet()
}

inline fun <reified T : Reporting> Collection<Reporting>.shouldReport(additional: (T) -> Unit = {}) {
    this.forOne {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}