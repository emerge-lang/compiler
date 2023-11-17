package matchers.compiler.negative

import compiler.binding.context.SoftwareContext
import compiler.binding.type.BuiltinType
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.SourceLocation
import compiler.lexer.lex
import compiler.parser.grammar.Module
import compiler.parser.toTransactional
import compiler.reportings.Reporting
import io.kotest.inspectors.forOne
import io.kotest.matchers.types.shouldBeInstanceOf

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
    val invokedFrom = Thread.currentThread().stackTrace[3]

    var moduleCode = code
    var nEmptyLinesToPrepend = invokedFrom.lineNumber
    if (addModuleDeclaration) {
        moduleCode = "module testmodule\n$code"
        nEmptyLinesToPrepend--
    }

    if (!moduleCode.endsWith("\n")) {
        moduleCode += "\n"
    }

    moduleCode = "\n".repeat(nEmptyLinesToPrepend) + moduleCode

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = invokedFrom.fileName
        override val sourceLines = moduleCode.split("\n")
    }
    val initialSourceLocation = SourceLocation(sourceDescriptor, invokedFrom.lineNumber + 1, 1)
    val result = Module.tryMatch(Unit, lex(moduleCode, sourceDescriptor).toTransactional(initialSourceLocation))
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