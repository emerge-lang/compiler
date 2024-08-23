package compiler.binding.context

import compiler.ast.ASTSourceFile
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: CanonicalElementName.Package,
    val softwareContext: SoftwareContext,
) : SemanticallyAnalyzable {
    private val seanHelper = SeanHelper()

    private val _sourceFiles: MutableSet<SourceFile> = HashSet()
    val sourceFiles: Set<SourceFile> = _sourceFiles

    fun addSourceFile(sourceFile: ASTSourceFile): SourceFile {
        val bound = sourceFile.bindTo(this)
        addSourceFile(bound)
        return bound
    }

    fun addSourceFile(sourceFile: SourceFile) {
        seanHelper.requirePhase1NotDone()
        _sourceFiles.add(sourceFile)
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            _sourceFiles.flatMap { it.semanticAnalysisPhase1() }
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            _sourceFiles.flatMap { it.semanticAnalysisPhase2() }
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            _sourceFiles.flatMap { it.semanticAnalysisPhase3() }
        }
    }

    val nonEmptyPackages: Sequence<PackageContext> get() = _sourceFiles
        .asSequence()
        .map { softwareContext.getPackage(it.packageName)!! }

    override fun toString() = moduleName.toString()

    fun toBackendIr(): IrModule = IrModuleImpl(this)
}