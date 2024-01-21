package compiler.binding.context

import compiler.InternalCompilerError
import compiler.PackageName
import compiler.reportings.Reporting
import java.util.HashSet

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: PackageName,
    val softwareContext: SoftwareContext,
) {
    private val _sourceFiles: MutableSet<SourceFile> = HashSet()
    val sourceFiles: Set<SourceFile> = _sourceFiles

    /**
     * Defines a new module with the given name and the given context.
     * @throws InternalCompilerError If such a module is already defined.
     * TODO: Create & use a more specific exception
     */
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