package compiler.binding.context

import compiler.ast.ASTSourceFile
import compiler.binding.SemanticallyAnalyzable
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.PackageName

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: PackageName,
    val softwareContext: SoftwareContext,
) : SemanticallyAnalyzable {
    private val _sourceFiles: MutableSet<SourceFile> = HashSet()
    val sourceFiles: Set<SourceFile> = _sourceFiles

    fun addSourceFile(sourceFile: ASTSourceFile): SourceFile {
        val bound = sourceFile.bindTo(this)
        _sourceFiles.add(bound)
        return bound
    }

    fun addSourceFile(sourceFile: SourceFile) {
        _sourceFiles.add(sourceFile)
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return _sourceFiles.flatMap { it.semanticAnalysisPhase1() }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return _sourceFiles.flatMap { it.semanticAnalysisPhase2() }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return _sourceFiles.flatMap { it.semanticAnalysisPhase3() }
    }

    override fun toString() = moduleName.toString()
}