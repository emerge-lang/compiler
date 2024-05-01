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
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ModuleSourceRef
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.noop.NoopBackend
import io.kotest.inspectors.forNone
import io.kotest.inspectors.forOne
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult
import io.kotest.matchers.collections.shouldBeEmpty
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

    val sourceFile = MemorySourceFile(invokedFrom.fileName!!, CanonicalElementName.Package(listOf("testmodule")), moduleCode)
    return lex(sourceFile)
}

private val defaultModulesParsed: List<Pair<CanonicalElementName.Package, List<ASTSourceFile>>> by lazy {
    (NoopBackend().targetSpecificModules + listOf(
        ModuleSourceRef(CoreIntrinsicsModule.SRC_DIR, CoreIntrinsicsModule.NAME),
        ModuleSourceRef(StandardLibraryModule.SRC_DIR, StandardLibraryModule.NAME),
    ))
        .map { module ->
            val sourceFiles = SourceSet.load(module.path, module.moduleName)
                .map {
                    val tokens = lex(it)
                    SourceFileRule.match(tokens, tokens.peek()!!.span.file)
                }
                .partition { it.hasErrors }
                .let { (withErrors, withoutErrors) ->
                    require(withErrors.isEmpty()) { "default module ${module.moduleName} has errors: ${withErrors.flatMap { it.reportings }.first { it.level >= Reporting.Level.ERROR}}" }
                    withoutErrors
                }
                .mapNotNull { it.item }

            module.moduleName to sourceFiles
        }
}


class IntegrationTestModule(
    val moduleName: CanonicalElementName.Package,
    val tokens: TokenSequence,
) {
    companion object {
        /**
         * To be invoked with this exact syntax to have the line numbers match
         *
         * ```
         * IntegrationTestModule.of("foo.module", """
         *     // source line 1
         * """.trimMargin())
         * ```
         */
        fun of(moduleName: String, code: String, definedAt: StackTraceElement = Thread.currentThread().stackTrace[2]): IntegrationTestModule {
            val moduleDotName = CanonicalElementName.Package(moduleName.split('.'))
            val sourceFile = MemorySourceFile(definedAt.fileName!!, moduleDotName, code.assureEndsWith('\n'))
            val tokens = lex(sourceFile)
            return IntegrationTestModule(moduleDotName, tokens)
        }
    }
}

fun emptySoftwareContext(validate: Boolean = true): SoftwareContext {
    val swCtxt = SoftwareContext()
    defaultModulesParsed.forEach { (moduleName, sources) ->
        val moduleCtx = swCtxt.registerModule(moduleName)
        sources.forEach(moduleCtx::addSourceFile)
    }

    if (validate) {
        swCtxt
            .doSemanticAnalysis()
            .find { it.level >= Reporting.Level.ERROR }
            ?.let {
                error("SoftwareContext without any user code contains errors:\n$it")
            }
    }

    return swCtxt
}

fun validateModules(vararg modules: IntegrationTestModule): Pair<SoftwareContext, Collection<Reporting>> {
    val swCtxt = emptySoftwareContext(false)

    val lexicalReportings = mutableListOf<Reporting>()
    modules.forEach { module ->
        val lexerSourceFile = module.tokens.peek()!!.span.file
        val result = SourceFileRule.match(module.tokens, lexerSourceFile)
        if (result.item == null) {
            val error = result.reportings.maxBy { it.level }
            throw AssertionError("Failed to parse code: ${error.message} in ${error.span}")
        }
        lexicalReportings.addAll(result.reportings)
        val sourceFile = result.item!!
        val nTopLevelDeclarations = sourceFile.functions.size + sourceFile.baseTypes.size + sourceFile.variables.size
        check(nTopLevelDeclarations > 0) { "Found no top-level declarations in the test source of module ${module.moduleName}. Very likely a parsing bug." }

        swCtxt.registerModule(module.moduleName).addSourceFile(sourceFile)
    }

    val semanticReportings = swCtxt.doSemanticAnalysis()
    return Pair(
        swCtxt,
        (lexicalReportings + semanticReportings).toSet(),
    )
}

/**
 * To be invoked with this exact syntax to have the line numbers match
 *
 * ```
 * VariableDeclaration.parseAndValidate("foo_module", """
 *     // source line 1
 * """.trimMargin())
 * ```
 */
fun validateModule(
    code: String,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
): Pair<SoftwareContext, Collection<Reporting>> {
    val module = IntegrationTestModule(CanonicalElementName.Package(listOf("testmodule")), lexCode(code.assureEndsWith('\n'), true, invokedFrom))
    return validateModules(module)
}

// TODO: most test cases expect EXACTLY one reporting, extra reportings are out-of-spec. This one lets extra reportings pass :(
// the trick is finding the test that actually want more than one reporting and adapting that test code
inline fun <reified T : Reporting> Pair<SoftwareContext, Collection<Reporting>>.shouldReport(additional: SoftwareContext.(T) -> Unit = {}): Pair<SoftwareContext, Collection<Reporting>> {
    second.shouldReport<T> {
        first.additional(it)
    }
    return this
}

inline fun <reified T : Reporting> Collection<Reporting>.shouldReport(additional: (T) -> Unit = {}): Collection<Reporting> {
    forOne {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
    return this
}

inline fun <reified T : Reporting> Pair<SoftwareContext, Collection<Reporting>>.shouldNotReport(additional: (T) -> Unit = {}): Pair<SoftwareContext, Collection<Reporting>> {
    second.shouldNotReport<T>(additional)
    return this
}

inline fun <reified T : Reporting> Collection<Reporting>.shouldNotReport(additional: (T) -> Unit = {}): Collection<Reporting> {
    forNone {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
    return this
}

fun Pair<SoftwareContext, Collection<Reporting>>.shouldHaveNoDiagnostics(): Pair<SoftwareContext, Collection<Reporting>> {
    second.shouldBeEmpty()
    return this
}

fun haveNoDiagnostics(): Matcher<Pair<SoftwareContext, Collection<Reporting>>> = object : Matcher<Pair<SoftwareContext, Collection<Reporting>>> {
    override fun test(value: Pair<SoftwareContext, Collection<Reporting>>): MatcherResult {
        return object : MatcherResult {
            override fun failureMessage() = run {
                val byLevel = value.second
                    .groupBy { it.level.name.lowercase() }
                    .entries
                    .joinToString { (level, reportings) -> "${reportings.size} ${level}s" }
                "there should not be any diagnostics, but found $byLevel"
            }
            override fun negatedFailureMessage() = "there should be diagnostics, but found none."
            override fun passed() = value.second.isEmpty()
        }
    }
}

fun Pair<SoftwareContext, Collection<Reporting>>.moduleBackendIrAssumingNoErrors(moduleName: String = "testmodule"): IrModule {
    check(second.none { it.level == Reporting.Level.ERROR })
    return first.toBackendIr().modules.single { it.name == CanonicalElementName.Package(listOf("testmodule")) }
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}