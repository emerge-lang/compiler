package compiler.binding

import compiler.ast.AstVisibility
import compiler.ast.DEFAULT_IMPORT_PACKAGES
import compiler.binding.context.CTContext
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.SourceFile
import compiler.lexer.Span
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

sealed class BoundVisibility : SemanticallyAnalyzable {
    protected abstract val context: CTContext
    abstract val astNode: AstVisibility

    /**
     * Validate whether an element with `this` visibility is accessible from
     * the given location ([accessAt]). [subject] is not inspected, only forwarded
     * to any [Diagnostic]s generated.
     *
     * **WARNING:** You very likely do not want to use this method, but [DefinitionWithVisibility.validateAccessFrom]
     * instead.
     */
    abstract fun validateAccessFrom(accessAt: Span, subject: DefinitionWithVisibility, diagnosis: Diagnosis)

    abstract fun isStrictlyBroaderThan(other: BoundVisibility): Boolean
    abstract fun isPossiblyBroaderThan(other: BoundVisibility): Boolean

    abstract fun withAstNode(newNode: AstVisibility): BoundVisibility

    fun coerceAtMost(other: BoundVisibility): BoundVisibility {
        if (this.isPossiblyBroaderThan(other)) {
            return other.withAstNode(this.astNode)
        }

        return this
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    /**
     * Assuming `this` visibility appears on [element], validates.
     */
    open fun validateOnElement(element: DefinitionWithVisibility, diagnosis: Diagnosis) {
        if (this.isStrictlyBroaderThan(context.visibility)) {
            diagnosis.add(Diagnostic.visibilityShadowed(element, context.visibility))
        }
    }

    class FileScope(override val context: CTContext, override val astNode: AstVisibility) : BoundVisibility() {
        val lexerFile: SourceFile get() = context.sourceFile.lexerFile
        override fun validateAccessFrom(accessAt: Span, subject: DefinitionWithVisibility, diagnosis: Diagnosis) {
            if (lexerFile != accessAt.sourceFile) {
                diagnosis.add(Diagnostic.elementNotAccessible(subject, this, accessAt))
            }
        }

        override fun isStrictlyBroaderThan(other: BoundVisibility) = false

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when(other) {
            is FileScope -> this.lexerFile != other.lexerFile
            else -> false
        }

        override fun withAstNode(newNode: AstVisibility): BoundVisibility {
            return FileScope(context, newNode)
        }

        override fun toString() = "private in file $lexerFile"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is FileScope) return false

            if (lexerFile != other.lexerFile) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + lexerFile.hashCode()
            return result
        }
    }

    class PackageScope(
        override val context: CTContext,
        val packageName: CanonicalElementName.Package,
        override val astNode: AstVisibility,
        val isDefault: Boolean,
    ) : BoundVisibility() {
        override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
            val owningModule = context.moduleContext.moduleName
            if (owningModule != packageName && owningModule.containsOrEquals(packageName)) {
                diagnosis.add(Diagnostic.visibilityTooBroad(owningModule, this))
            }
        }

        override fun validateAccessFrom(accessAt: Span, subject: DefinitionWithVisibility, diagnosis: Diagnosis) {
            if (packageName.containsOrEquals(accessAt.sourceFile.packageName)) {
                validateCrossModuleAccess(context, accessAt, subject, diagnosis)
            } else {
                diagnosis.add(Diagnostic.elementNotAccessible(subject, this, accessAt))
            }
        }

        override fun validateOnElement(element: DefinitionWithVisibility, diagnosis: Diagnosis) {
            if (isDefault) {
                return
            }

            return super.validateOnElement(element, diagnosis)
        }

        override fun isStrictlyBroaderThan(other: BoundVisibility) = when(other) {
            is FileScope -> true
            is PackageScope -> packageName != other.packageName && packageName.containsOrEquals(other.packageName)
            is ExportedScope -> false
        }

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when(other) {
            is FileScope -> true
            is PackageScope -> !(packageName.containsOrEquals(other.packageName))
            is ExportedScope -> false
        }

        override fun withAstNode(newNode: AstVisibility): BoundVisibility {
            return PackageScope(context, packageName, newNode, isDefault)
        }

        override fun toString() = "internal to package $packageName"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is PackageScope) return false

            if (packageName != other.packageName) return false

            return true
        }

        override fun hashCode(): Int {
            var result = javaClass.hashCode()
            result = 31 * result + packageName.hashCode()
            return result
        }
    }

    class ExportedScope(
        override val context: CTContext,
        override val astNode: AstVisibility,
    ) : BoundVisibility() {
        override fun validateAccessFrom(accessAt: Span, subject: DefinitionWithVisibility, diagnosis: Diagnosis) {
            validateCrossModuleAccess(context, accessAt, subject, diagnosis)
        }

        override fun isStrictlyBroaderThan(other: BoundVisibility) = when (other) {
            is ExportedScope -> false
            else -> true
        }

        override fun isPossiblyBroaderThan(other: BoundVisibility) = when (other) {
            is ExportedScope -> false
            else -> true
        }

        override fun withAstNode(newNode: AstVisibility): BoundVisibility {
            return ExportedScope(context, astNode)
        }

        override fun toString() = "exported"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is ExportedScope) return false

            return true
        }

        override fun hashCode(): Int {
            return javaClass.hashCode()
        }
    }

    companion object {
        fun default(context: CTContext): BoundVisibility {
            return PackageScope(context, context.moduleContext.moduleName, AstVisibility.Module(KeywordToken(Keyword.MODULE)), true)
        }
    }
}

private fun validateCrossModuleAccess(contextOfAccessedElement: CTContext, accessAt: Span, subject: DefinitionWithVisibility, diagnosis: Diagnosis) {
    val moduleOfAccessedElement = contextOfAccessedElement.moduleContext
    val moduleOfAccess = contextOfAccessedElement.swCtx.getModuleOfPackage(accessAt.sourceFile.packageName)
    if (moduleOfAccess == moduleOfAccessedElement) {
        return
    }

    // always allow accessing emerge.std and emerge.core
    if (moduleOfAccessedElement.moduleName in DEFAULT_IMPORT_PACKAGES || DEFAULT_IMPORT_PACKAGES.any { it.containsOrEquals(moduleOfAccessedElement.moduleName) }) {
        return
    }

    // always allow accessing emerge.platform
    if (EmergeConstants.PLATFORM_MODULE_NAME.containsOrEquals(moduleOfAccessedElement.moduleName)) {
        return
    }

    if (moduleOfAccessedElement.moduleName in moduleOfAccess.explicitlyDependsOnModules) {
        return
    }

    diagnosis.add(Diagnostic.missingModuleDependency(subject, accessAt, moduleOfAccessedElement.moduleName, moduleOfAccess.moduleName))
}