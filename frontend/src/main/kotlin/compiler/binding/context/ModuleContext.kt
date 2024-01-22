package compiler.binding.context

import compiler.PackageName
import compiler.ast.ASTSourceFile
import compiler.reportings.Reporting

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: PackageName,
    val softwareContext: SoftwareContext,
) {
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

    fun doSemanticAnalysis(): Collection<Reporting> {
        return (_sourceFiles.flatMap { it.semanticAnalysisPhase1() } +
                _sourceFiles.flatMap { it.semanticAnalysisPhase2() } +
                _sourceFiles.flatMap { it.semanticAnalysisPhase3() })
            .toSet()
    }

    override fun toString() = moduleName.toString()
}