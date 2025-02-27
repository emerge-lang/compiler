package compiler.binding.context

import compiler.ast.ASTSourceFile
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.reportings.Diagnosis
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * Bundles all source files of a single module.
 */
class ModuleContext(
    val moduleName: CanonicalElementName.Package,
    /** explicit dependencies of this module. Validating and supplying this is considered a task of the build tool, not the user. */
    val explicitlyDependsOnModules: Set<CanonicalElementName.Package>,
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

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            _sourceFiles.forEach { it.semanticAnalysisPhase1(diagnosis) }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            _sourceFiles.forEach { it.semanticAnalysisPhase2(diagnosis) }
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            _sourceFiles.forEach { it.semanticAnalysisPhase3(diagnosis) }
        }
    }

    val nonEmptyPackages: Sequence<PackageContext> get() = _sourceFiles
        .asSequence()
        .map { softwareContext.getPackage(it.packageName)!! }

    override fun toString() = moduleName.toString()

    fun toBackendIr(): IrModule = IrModuleImpl(this)
}