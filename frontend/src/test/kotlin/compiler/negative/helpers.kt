package compiler.compiler.negative

import compiler.ast.ASTSourceFile
import compiler.binding.context.ModuleContext
import compiler.binding.context.SoftwareContext
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.lexer.MemoryLexerSourceFile
import compiler.lexer.SourceSet
import compiler.lexer.Token
import compiler.lexer.lex
import compiler.parser.SourceFileRule
import compiler.parser.grammar.rule.MatchingResult
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.noop.NoopBackend
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants
import io.github.tmarsteel.emerge.common.config.ConfigModuleDefinition
import io.kotest.assertions.fail
import io.kotest.inspectors.forAtLeastOne
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

    val sourceFile = MemoryLexerSourceFile(invokedFrom.fileName!!, CanonicalElementName.Package(listOf("testmodule")), moduleCode)
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
                    require(errors.isEmpty()) { "default module ${module.name} has errors: ${errors.map { (it as MatchingResult.Error).diagnostic }}" }
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
        fun of(
            moduleName: String,
            code: String,
            uses: Set<CanonicalElementName.Package> = emptySet(),
            definedAt: StackTraceElement = Thread.currentThread().stackTrace[2]
        ): IntegrationTestModule {
            val moduleDotName = CanonicalElementName.Package(moduleName.split('.'))
            val sourceFile = MemoryLexerSourceFile(definedAt.fileName!!, moduleDotName, code.assureEndsWith('\n'))
            val tokens = lex(sourceFile)
            return IntegrationTestModule(moduleDotName, uses, tokens)
        }
    }
}

fun emptySoftwareContext(validate: Boolean = true, noStd: Boolean = false): SoftwareContext {
    val swCtxt = SoftwareContext()
    defaultModulesParsed
        .filter {
            return@filter !(noStd && it.first.name == EmergeConstants.STD_MODULE_NAME)
        }
        .forEach { (module, sources) ->
            val moduleCtx = swCtxt.registerModule(module.name, module.uses)
            sources.forEach(moduleCtx::addSourceFile)
        }

    if (validate) {
        swCtxt.doSemanticAnalysis(FailOnErrorDiagnosis)
    }

    return swCtxt
}

fun IntegrationTestModule.parseAsOneSourceFileOfMultiple(): ASTSourceFile {
    val lexerSourceFile = tokens.first().span.sourceFile
    val result = SourceFileRule.match(tokens, lexerSourceFile)
    if (result is MatchingResult.Error) {
        throw AssertionError("Failed to parse code: ${result.diagnostic}")
    }
    result as MatchingResult.Success<ASTSourceFile>
    val sourceFile = result.item
    val nTopLevelDeclarations = sourceFile.functions.size + sourceFile.baseTypes.size + sourceFile.globalVariables.size
    check(nTopLevelDeclarations > 0) { "Found no top-level declarations in the test source of module ${moduleName}. Very likely a parsing bug." }

    return result.item
}

fun SoftwareContext.registerModule(module: IntegrationTestModule): ModuleContext {
    val astSourceFile = module.parseAsOneSourceFileOfMultiple()

    val moduleCtx = registerModule(module.moduleName, module.dependsOnModules)
    moduleCtx.addSourceFile(astSourceFile)

    return moduleCtx
}

fun validateModules(vararg modules: IntegrationTestModule, noStd: Boolean = false): Pair<SoftwareContext, Collection<Diagnostic>> {
    val swCtxt = emptySoftwareContext(false, noStd)

    modules.forEach {
        swCtxt.registerModule(it)
    }

    val diagnosis = CollectingDiagnosis()
    swCtxt.doSemanticAnalysis(diagnosis)
    return Pair(
        swCtxt,
        diagnosis.findings.toSet(),
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
    noStd: Boolean = false,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
): Pair<SoftwareContext, Collection<Diagnostic>> {
    val module = IntegrationTestModule(CanonicalElementName.Package(listOf("testmodule")), emptySet(), lexCode(code.assureEndsWith('\n'), true, invokedFrom))
    return validateModules(module, noStd = noStd)
}

fun useValidModule(
    code: String,
    noStd: Boolean = false,
    invokedFrom: StackTraceElement = Thread.currentThread().stackTrace[2],
) : SoftwareContext {
    return validateModule(code, noStd, invokedFrom).shouldHaveNoDiagnostics().first
}

// TODO: most test cases expect EXACTLY one diagnostic, extra diagnostics are out-of-spec. This one lets extra reportings pass :(
// the trick is finding the test that actually want more than one diagnostic and adapting that test code
inline fun <reified T : Diagnostic> Pair<SoftwareContext, Collection<Diagnostic>>.shouldFind(allowMultiple: Boolean = false, additional: SoftwareContext.(T) -> Unit = {}): Pair<SoftwareContext, Collection<Diagnostic>> {
    second.shouldFind<T>(allowMultiple) {
        first.additional(it)
    }
    return this
}

inline fun <reified T : Diagnostic> Collection<Diagnostic>.shouldFind(allowMultiple: Boolean = false, additional: (T) -> Unit = {}): Collection<Diagnostic> {
    if (allowMultiple) {
        forAtLeastOne {
            it.shouldBeInstanceOf<T>()
            additional(it)
        }
    } else {
        forOne {
            it.shouldBeInstanceOf<T>()
            additional(it)
        }
    }
    return this
}

inline fun <reified T : Diagnostic> Pair<SoftwareContext, Collection<Diagnostic>>.shouldNotFind(additional: (T) -> Unit = {}): Pair<SoftwareContext, Collection<Diagnostic>> {
    second.shouldNotFind<T>(additional)
    return this
}

inline fun <reified T : Diagnostic> Collection<Diagnostic>.shouldNotFind(additional: (T) -> Unit = {}): Collection<Diagnostic> {
    forNone {
        it.shouldBeInstanceOf<T>()
        additional(it)
    }
    return this
}

object FailTestOnFindingDiagnosis : Diagnosis {
    override val nErrors = 0uL

    override fun add(finding: Diagnostic) {
        fail("Expected no findings, but got this:\n$finding")
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return other === this || other.hasSameDrainAs(this)
    }
}

object FailOnErrorDiagnosis : Diagnosis {
    override val nErrors = 0uL

    override fun add(finding: Diagnostic) {
        if (finding.severity >= Diagnostic.Severity.ERROR) {
            fail("Expected no errors, but got this:\n$finding")
        }
    }

    override fun hasSameDrainAs(other: Diagnosis): Boolean {
        return other === this || other.hasSameDrainAs(this)
    }
}

fun Pair<SoftwareContext, Collection<Diagnostic>>.shouldHaveNoDiagnostics(
    allowedSeverities: Set<Diagnostic.Severity> = setOf(Diagnostic.Severity.CONSECUTIVE),
): Pair<SoftwareContext, Collection<Diagnostic>> {
    second.filter { it.severity !in allowedSeverities }.shouldBeEmpty()
    return this
}

fun haveNoDiagnostics(allowedSeverities: Set<Diagnostic.Severity> = setOf(Diagnostic.Severity.CONSECUTIVE)): Matcher<Pair<SoftwareContext, Collection<Diagnostic>>> = object : Matcher<Pair<SoftwareContext, Collection<Diagnostic>>> {
    override fun test(value: Pair<SoftwareContext, Collection<Diagnostic>>): MatcherResult {
        return object : MatcherResult {
            override fun failureMessage() = run {
                val byLevel = value.second
                    .groupBy { it.severity }
                    .entries
                    .filter { (sev, _) -> sev !in allowedSeverities }
                    .joinToString { (severity, diagnostics) -> "${diagnostics.size} ${severity.name.lowercase()}s" }
                "there should not be any diagnostics, but found $byLevel"
            }
            override fun negatedFailureMessage() = "there should be diagnostics, but found none."
            override fun passed() = value.second.isEmpty()
        }
    }
}

inline fun <reified T : Diagnostic> Pair<SoftwareContext, Collection<Diagnostic>>.ignore(): Pair<SoftwareContext, Collection<Diagnostic>> {
    return Pair(first, second.filter { it !is T })
}

fun Pair<SoftwareContext, Collection<Diagnostic>>.moduleBackendIrAssumingNoErrors(moduleName: String = "testmodule"): IrModule {
    check(second.none { it.severity == Diagnostic.Severity.ERROR })
    return first.toBackendIr().modules.single { it.name == CanonicalElementName.Package(listOf("testmodule")) }
}

private fun String.assureEndsWith(suffix: Char): String {
    return if (endsWith(suffix)) this else this + suffix
}