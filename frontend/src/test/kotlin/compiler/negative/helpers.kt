package compiler.compiler.negative

import compiler.ast.ASTSourceFile
import compiler.binding.context.SoftwareContext
import compiler.lexer.MemorySourceFile
import compiler.lexer.SourceSet
import compiler.lexer.Token
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.grammar.rule.MatchingResult
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.noop.NoopBackend
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition
import io.kotest.inspectors.forNone
import io.kotest.inspectors.forOne
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.types.shouldBeInstanceOf
import java.nio.file.Paths

fun lexCode(
    code: String,
    addPackageDeclaration: Boolean = true,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
): Array<Token> {
    val moduleCode = if (addPackageDeclaration) {
        require(invokedFrom.lineNumber > 1) {
            "Test code is declared at line 1, cannot both add a module declaration AND keep the source line numbers in sync"
        }
        "package testmodule\n" + "\n".repeat(invokedFrom.lineNumber - 1) + code
    } else {
        code
    }

    val sourceFile = MemorySourceFile(invokedFrom.fileName!!, CanonicalElementName.Package(listOf("testmodule")), moduleCode)
    return lex(sourceFile, addTrailingNewline = addPackageDeclaration)
}

private val noopBackendConfig = NoopBackend.Config(
    platformSources = Paths.get(System.getProperty("emerge.backend.noop.platform.sources"))
)
private val defaultModulesParsed: List<Pair<ConfigModuleDefinition, List<ASTSourceFile>>> by lazy {
    (NoopBackend().getTargetSpecificModules(noopBackendConfig, Unit) + listOf(
        ConfigModuleDefinition(EmergeConstants.CORE_MODULE_NAME, Paths.get(System.getProperty("emerge.frontend.core.sources"))),
        ConfigModuleDefinition(EmergeConstants.STD_MODULE_NAME, Paths.get(System.getProperty("emerge.frontend.std.sources"))),
    ))
        .map { module ->
            val sourceFiles = SourceSet.load(module.sourceDirectory, module.name)
                .map {
                    val tokens = lex(it)
                    SourceFileRule.match(tokens, tokens.first().span.sourceFile)
                }
                .partition { it is MatchingResult.Error }
                .let { (errors, successes) ->
                    require(errors.isEmpty()) { "default module ${module.name} has errors: ${errors.map { (it as MatchingResult.Error).reporting }}" }
                    successes as List<MatchingResult.Success<ASTSourceFile>>
                }
                .map { it.item }

            module to sourceFiles
        }
}


class IntegrationTestModule(
    val moduleName: CanonicalElementName.Package,
    val dependsOnModules: Set<CanonicalElementName.Package>,
    val tokens: Array<Token>,
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
        fun of(moduleName: String, code: String, uses: Set<CanonicalElementName.Package> = emptySet(), definedAt: StackTraceElement = Thread.currentThread().stackTrace[2]): IntegrationTestModule {
            val moduleDotName = CanonicalElementName.Package(moduleName.split('.'))
            val sourceFile = MemorySourceFile(definedAt.fileName!!, moduleDotName, code.assureEndsWith('\n'))
            val tokens = lex(sourceFile)
            return IntegrationTestModule(moduleDotName, uses, tokens)
        }
    }
}

fun emptySoftwareContext(validate: Boolean = true): SoftwareContext {
    val swCtxt = SoftwareContext()
    defaultModulesParsed.forEach { (module, sources) ->
        val moduleCtx = swCtxt.registerModule(module.name, module.uses)
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

    modules.forEach { module ->
        val lexerSourceFile = module.tokens.first().span.sourceFile
        val result = SourceFileRule.match(module.tokens, lexerSourceFile)
        if (result is MatchingResult.Error) {
            throw AssertionError("Failed to parse code: ${result.reporting}")
        }
        result as MatchingResult.Success<ASTSourceFile>
        val sourceFile = result.item
        val nTopLevelDeclarations = sourceFile.functions.size + sourceFile.baseTypes.size + sourceFile.globalVariables.size
        check(nTopLevelDeclarations > 0) { "Found no top-level declarations in the test source of module ${module.moduleName}. Very likely a parsing bug." }

        swCtxt.registerModule(module.moduleName, module.dependsOnModules).addSourceFile(sourceFile)
    }

    val semanticReportings = swCtxt.doSemanticAnalysis()
    return Pair(
        swCtxt,
        semanticReportings.toSet(),
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
    val module = IntegrationTestModule(CanonicalElementName.Package(listOf("testmodule")), emptySet(), lexCode(code.assureEndsWith('\n'), true, invokedFrom))
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

inline fun <reified T : Reporting> Pair<SoftwareContext, Collection<Reporting>>.ignore(): Pair<SoftwareContext, Collection<Reporting>> {
    return Pair(first, second.filter { it !is T })
}

fun Pair<SoftwareContext, Collection<Reporting>>.moduleBackendIrAssumingNoErrors(moduleName: String = "testmodule"): IrModule {
    check(second.none { it.level == Reporting.Level.ERROR })
    return first.toBackendIr().modules.single { it.name == CanonicalElementName.Package(listOf("testmodule")) }
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}