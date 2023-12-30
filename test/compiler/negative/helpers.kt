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

fun lexCode(
    code: String,
    addModuleDeclaration: Boolean = true,
    initialSourceLocation: SourceLocation = getInvokedFromAsSourceLocationForParameterDefaultValue(),
): TokenSequence {
    return lexCodeInternal(code, addModuleDeclaration, initialSourceLocation)
}

fun getInvokedFromAsSourceLocationForParameterDefaultValue(): SourceLocation {
    val invokedFrom = Thread.currentThread().stackTrace[3]
    return SourceLocation(
        object : SourceDescriptor {
            override val sourceLocation = invokedFrom.fileName
        },
        invokedFrom.lineNumber,
        1,
    )
}

private fun lexCodeInternal(
    code: String,
    addModuleDeclaration: Boolean,
    initialSourceLocation: SourceLocation,
): TokenSequence {
    val moduleCode = if (addModuleDeclaration) {
        require(initialSourceLocation.sourceLine > 1) {
            "Test code is declared at line 1, cannot both add a module declaration AND keep the source line numbers in sync"
        }
        "module testmodule\n" + "\n".repeat(initialSourceLocation.sourceLine - 1) + code
    } else {
        code
    }

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
fun validateModule(
    code: String,
    addModuleDeclaration: Boolean = true,
    initialSourceLocation: SourceLocation = getInvokedFromAsSourceLocationForParameterDefaultValue(),
): Collection<Reporting> {
    val tokens = lexCodeInternal(code.assureEndsWith('\n'), addModuleDeclaration, initialSourceLocation)
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

// TODO: most test cases expect EXACTLY one reporting, extra reportings are out-of-spec. This one lets extra reportings pass :(
// the trick is finding the test that actually want more than one reporting and adapting that test code
inline fun <reified T : Reporting> Collection<Reporting>.shouldReport(additional: (T) -> Unit = {}) {
    this.forOne {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}