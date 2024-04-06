package compiler.binding

import compiler.ast.AstVisibility
import compiler.binding.context.CTContext
import compiler.binding.context.ModuleContext
import compiler.lexer.SourceFile
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

sealed interface BoundVisibility : SemanticallyAnalyzable {
    /**
     * Validate whether an element with `this` visibility is accessible from
     * the given location ([accessAt]). [subject] is not inspected, only forwarded
     * to any [Reporting]s generated.
     *
     * **WARNING:** You very likely do not want to use this method, but [DefinitionWithVisibility.validateAccessFrom]
     * instead.
     */
    fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting>

    override fun semanticAnalysisPhase1() = emptySet<Reporting>()
    override fun semanticAnalysisPhase2() = emptySet<Reporting>()
    override fun semanticAnalysisPhase3() = emptySet<Reporting>()

    class FileScope(val context: CTContext) : BoundVisibility {
        val lexerFile: SourceFile get() = context.sourceFile.lexerFile
        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            if (lexerFile == accessAt.file) {
                return emptySet()
            }

            return setOf(Reporting.elementNotAccessible(subject, this, accessAt))
        }
    }

    class ModuleScope(val moduleName: DotName) : BoundVisibility {
        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            if (moduleName.containsOrEquals(accessAt.file.packageName)) {
                return emptySet()
            }

            return setOf(Reporting.elementNotAccessible(subject, this, accessAt))
        }
    }

    class PackageScope(
        val moduleContext: ModuleContext,
        val astNode: AstVisibility.Package,
    ) : BoundVisibility {
        val packageName = astNode.packageName.asDotName

        override fun semanticAnalysisPhase1(): Set<Reporting> {
            val owningModule = moduleContext.moduleName
            if (owningModule.containsOrEquals(packageName)) {
                return setOf(Reporting.visibilityTooBroad(owningModule, this))
            }

            return emptySet()
        }

        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            if (packageName.containsOrEquals(accessAt.file.packageName)) {
                return emptySet()
            }

            return setOf(Reporting.elementNotAccessible(subject, this, accessAt))
        }
    }

    object ExportedScope : BoundVisibility {
        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            return emptySet()
        }
    }

    companion object {
        fun default(context: CTContext): BoundVisibility {
            return ModuleScope(context.moduleContext.moduleName)
        }
    }
}