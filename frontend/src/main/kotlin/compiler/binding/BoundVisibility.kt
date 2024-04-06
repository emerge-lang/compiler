package compiler.binding

import compiler.ast.AstVisibility
import compiler.binding.context.CTContext
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.SourceFile
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

sealed class BoundVisibility : SemanticallyAnalyzable {
    protected abstract val context: CTContext
    abstract val astNode: AstVisibility

    /**
     * Validate whether an element with `this` visibility is accessible from
     * the given location ([accessAt]). [subject] is not inspected, only forwarded
     * to any [Reporting]s generated.
     *
     * **WARNING:** You very likely do not want to use this method, but [DefinitionWithVisibility.validateAccessFrom]
     * instead.
     */
    abstract fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting>

    abstract fun isStrictlyBroarderThan(other: BoundVisibility): Boolean
    abstract fun isPossiblyBroaderThan(other: BoundVisibility): Boolean

    override fun semanticAnalysisPhase1() = emptySet<Reporting>()
    override fun semanticAnalysisPhase2() = emptySet<Reporting>()
    override fun semanticAnalysisPhase3() = emptySet<Reporting>()

    /**
     * Assuming `this` visibility appears on [element], validates.
     */
    open fun validateOnElement(element: DefinitionWithVisibility): Collection<Reporting> {
        if (this.isStrictlyBroarderThan(context.visibility)) {
            return setOf(Reporting.visibilityShadowed(element, context.visibility))
        }

        return emptySet()
    }

    class FileScope(override val context: CTContext, override val astNode: AstVisibility) : BoundVisibility() {
        val lexerFile: SourceFile get() = context.sourceFile.lexerFile
        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            if (lexerFile == accessAt.file) {
                return emptySet()
            }

            return setOf(Reporting.elementNotAccessible(subject, this, accessAt))
        }

        override fun isStrictlyBroarderThan(other: BoundVisibility) = false

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when(other) {
            is FileScope -> this.lexerFile != other.lexerFile
            else -> false
        }

        override fun toString() = "private in file $lexerFile"
    }

    class PackageScope(
        override val context: CTContext,
        val packageName: DotName,
        override val astNode: AstVisibility,
        val isDefault: Boolean,
    ) : BoundVisibility() {
        override fun semanticAnalysisPhase1(): Set<Reporting> {
            val owningModule = context.moduleContext.moduleName
            if (owningModule != packageName && owningModule.containsOrEquals(packageName)) {
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

        override fun validateOnElement(element: DefinitionWithVisibility): Collection<Reporting> {
            if (isDefault) {
                return emptySet()
            }

            return super.validateOnElement(element)
        }

        override fun isStrictlyBroarderThan(other: BoundVisibility) = when(other) {
            is FileScope -> true
            is PackageScope -> packageName != other.packageName && packageName.containsOrEquals(other.packageName)
            is ExportedScope -> false
        }

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when(other) {
            is FileScope -> true
            is PackageScope -> !(packageName.containsOrEquals(other.packageName))
            is ExportedScope -> false
        }

        override fun toString() = "internal to package $packageName"
    }

    class ExportedScope(
        override val context: CTContext,
        override val astNode: AstVisibility,
    ) : BoundVisibility() {
        override fun validateAccessFrom(accessAt: SourceLocation, subject: DefinitionWithVisibility): Collection<Reporting> {
            return emptySet()
        }

        override fun isStrictlyBroarderThan(other: BoundVisibility) = when (other) {
            is ExportedScope -> false
            else -> true
        }

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when (other) {
            is ExportedScope -> false
            else -> true
        }

        override fun toString() = "exported"
    }

    companion object {
        fun default(context: CTContext): BoundVisibility {
            return PackageScope(context, context.moduleContext.moduleName, AstVisibility.Module(KeywordToken(Keyword.MODULE)), true)
        }
    }
}