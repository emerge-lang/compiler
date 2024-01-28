package compiler.compiler.negative

import compiler.CoreIntrinsicsModule
import compiler.StandardLibraryModule
import compiler.ast.ASTSourceFile
import compiler.binding.context.SoftwareContext
import compiler.lexer.MemorySourceFile
import compiler.lexer.SourceSet
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.TokenSequence
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.noop.NoopBackend
import io.kotest.inspectors.forOne
import io.kotest.matchers.types.shouldBeInstanceOf

fun lexCode(
    code: String,
    addPackageDeclaration: Boolean = true,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
): TokenSequence {
    val moduleCode = if (addPackageDeclaration) {
        require(invokedFrom.lineNumber > 1) {
            "Test code is declared at line 1, cannot both add a module declaration AND keep the source line numbers in sync"
        }
        "package testmodule\n" + "\n".repeat(invokedFrom.lineNumber - 1) + code
    } else {
        code
    }

    val sourceFile = MemorySourceFile(invokedFrom.fileName!!, PackageName(listOf("testmodule")), moduleCode)
    return lex(sourceFile)
}

private val defaultModulesParsed: List<Pair<PackageName, List<ASTSourceFile>>> = (NoopBackend().targetSpecificModules + listOf(
    ModuleSourceRef(CoreIntrinsicsModule.SRC_DIR, CoreIntrinsicsModule.NAME),
    ModuleSourceRef(StandardLibraryModule.SRC_DIR, StandardLibraryModule.NAME),
))
    .map { module ->
        val sourceFiles = SourceSet.load(module.path, module.moduleName)
            .map { SourceFileRule.match(lex(it), it.packageName) }
            .partition { it.hasErrors }
            .let { (withErrors, withoutErrors) ->
                require(withErrors.isEmpty()) { "default module ${module.moduleName} has errors: ${withErrors.flatMap { it.reportings }.first { it.level >= Reporting.Level.ERROR}}" }
                withoutErrors
            }
            .mapNotNull { it.item }

        module.moduleName to sourceFiles
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
    addPackageDeclaration: Boolean = true,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
): Collection<Reporting> {
    val tokens = lexCode(code.assureEndsWith('\n'), addPackageDeclaration, invokedFrom)
    val result = SourceFileRule.match(tokens, PackageName(listOf("testmodule")))
    if (result.item == null) {
        val error = result.reportings.maxBy { it.level }
        throw AssertionError("Failed to parse code: ${error.message} in ${error.sourceLocation}")
    }
    val lexicalReportings = result.reportings
    val sourceFile = result.item!!
    val nTopLevelDeclarations = sourceFile.functions.size + sourceFile.structs.size + sourceFile.variables.size
    check(nTopLevelDeclarations > 0) { "Found no top-level declarations in the test source. Very likely a parsing bug." }

    val swCtxt = SoftwareContext()
    defaultModulesParsed.forEach { (moduleName, sources) ->
        val moduleCtx = swCtxt.registerModule(moduleName)
        sources.forEach(moduleCtx::addSourceFile)
    }
    CoreIntrinsicsModule.amendCoreModuleIn(swCtxt)
    swCtxt.registerModule(sourceFile.expectedPackageName).addSourceFile(sourceFile)

    val semanticReportings = swCtxt.doSemanticAnalysis()
    return (lexicalReportings + semanticReportings).toSet()
}

// TODO: most test cases expect EXACTLY one reporting, extra reportings are out-of-spec. This one lets extra reportings pass :(
// the trick is finding the test that actually want more than one reporting and adapting that test code
inline fun <reified T : Reporting> Collection<Reporting>.shouldReport(additional: (T) -> Unit = {}): Collection<Reporting> {
    this.forOne {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
    return this
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}