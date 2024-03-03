package compiler.binding.context

import compiler.OnceAction
import compiler.ast.ASTSourceFile
import compiler.binding.SemanticallyAnalyzable
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrModule

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: DotName,
    val softwareContext: SoftwareContext,
) : SemanticallyAnalyzable {
    private val onceAction = OnceAction()

    private val _sourceFiles: MutableSet<SourceFile> = HashSet()
    val sourceFiles: Set<SourceFile> = _sourceFiles

    fun addSourceFile(sourceFile: ASTSourceFile): SourceFile {
        val bound = sourceFile.bindTo(this)
        addSourceFile(bound)
        return bound
    }

    fun addSourceFile(sourceFile: SourceFile) {
        onceAction.requireActionNotDone(OnceAction.SemanticAnalysisPhase1)
        _sourceFiles.add(sourceFile)
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            _sourceFiles.flatMap { it.semanticAnalysisPhase1() }
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            _sourceFiles.flatMap { it.semanticAnalysisPhase2() }
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            _sourceFiles.flatMap { it.semanticAnalysisPhase3() }
        }
    }

    override fun toString() = moduleName.toString()

    fun toBackendIr(): IrModule = IrModuleImpl(this)
}