package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundLoop
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundMixinStatement
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.ErroneousType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.mixinNotAllowed
import io.github.tmarsteel.emerge.common.CanonicalElementName

class SourceFileRootContext(
    packageContext: PackageContext,
    declaredOrInferredPackageName: CanonicalElementName.Package,
) : MutableExecutionScopedCTContext(
    SourceFileParentContext(packageContext),
    true,
    false,
    ExecutionScopedCTContext.Repetition.EXACTLY_ONCE,
) {
    override val packageName: CanonicalElementName.Package = declaredOrInferredPackageName
    override lateinit var sourceFile: SourceFile

    val variables: Collection<BoundVariable> = _variables.values
    val functions: Collection<BoundDeclaredFunction> = _functions
    val types: Collection<BoundBaseType> = _types

    override fun addDeferredCode(code: DeferrableExecutable) {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getContextLocalDeferredCode(): Sequence<DeferrableExecutable> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getScopeLocalDeferredCode(): Sequence<DeferrableExecutable> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getFunctionDeferredCode(): Sequence<DeferrableExecutable> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    private val ambiguousSimpleNamesByImport = HashSet<String>()
    fun markSimpleNameAmbiguousByImports(simpleName: String) {
        ambiguousSimpleNamesByImport.add(simpleName)
    }
    override fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean {
        return simpleName in ambiguousSimpleNamesByImport || parentContext.hasAmbiguousImportOrDeclarationsForSimpleName(simpleName)
    }

    private companion object {
        val EMPTY = object : ExecutionScopedCTContext {
            override val swCtx: SoftwareContext
                get() = throw InternalCompilerError("${this::swCtx.name} not available")

            override val moduleContext: ModuleContext
                get() = throw InternalCompilerError("${this::moduleContext.name} not available")

            override val packageName: CanonicalElementName.Package
                get() = throw InternalCompilerError("${this::packageName.name} not available")

            override val sourceFile: SourceFile
                get() = throw InternalCompilerError("file not initialized yet")

            override val visibility: BoundVisibility
                get() = throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")

            override val isScopeBoundary = false
            override val isFunctionRoot = false
            override val isExceptionHandler = false
            override val hasExceptionHandler = false
            override val repetitionRelativeToParent = ExecutionScopedCTContext.Repetition.EXACTLY_ONCE
            override val imports = emptySet<BoundImportDeclaration>()
            override val allTypeParameters = emptySequence<BoundTypeParameter>()

            override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? = null
            override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean = false
            override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? = null
            override fun resolveBaseType(simpleName: String): Sequence<BoundBaseType> = emptySequence()
            override fun hasUnresolvableImportForSimpleName(simpleName: String): Boolean {
                return false
            }
            override fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean {
                return false
            }

            override fun resolveType(ref: TypeReference): BoundTypeReference = ErroneousType(
                this,
                when (ref) {
                    is AstSimpleTypeReference -> ref
                    is AstIntersectionType -> ref.components.first()
                },
                (ref as? NamedTypeReference)?.arguments?.map { resolveTypeArgument(it, null) },
                emptyList(),
            )
            override fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet<*>> = emptySet()

            override fun getContextLocalDeferredCode(): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getScopeLocalDeferredCode(): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getExceptionHandlingLocalDeferredCode(): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getDeferredCodeForThrow(): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getDeferredCodeForBreakOrContinue(parentLoop: BoundLoop<*>): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }

            override fun getFunctionDeferredCode(): Sequence<DeferrableExecutable> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }

            override fun addDeferredCode(code: DeferrableExecutable) {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }

            override fun getRepetitionBehaviorRelativeTo(indirectParent: CTContext) = ExecutionScopedCTContext.Repetition.EXACTLY_ONCE

            override val parentLoop = null

            override fun registerMixin(
                mixinStatement: BoundMixinStatement,
                type: BoundTypeReference,
                diagnosis: Diagnosis
            ): ExecutionScopedCTContext.MixinRegistration? {
                diagnosis.mixinNotAllowed(mixinStatement)
                return null
            }

            override fun toString() = "SourceFileRootContext[${sourceFile.lexerFile}]"
        }
    }

    private class SourceFileParentContext(val packageContext: PackageContext) : ExecutionScopedCTContext by EMPTY {
        override val moduleContext = packageContext.moduleContext

        override val visibility = BoundVisibility.default(this)

        override val sourceFile: SourceFile
            get() = throw InternalCompilerError("shouldn't be accessed")

        override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
            if (fromOwnFileOnly) {
                return EMPTY.resolveVariable(name, fromOwnFileOnly)
            }

            return packageContext.resolveVariable(name)
        }

        override fun resolveBaseType(simpleName: String): Sequence<BoundBaseType> {
            return sequenceOf(packageContext.resolveBaseType(simpleName)).filterNotNull()
        }

        override fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean {
            val fromTypes = packageContext.types
                .filter { it.simpleName == simpleName }
                .take(2)
                .count() > 1
            if (fromTypes) {
                return true
            }

            val fromVars = packageContext.globalVariables
                .filter { it.name == simpleName }
                .take(2)
                .count() > 1
            if (fromVars) {
                return true
            }

            return false
        }

        override fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet<*>> {
            return packageContext.getTopLevelFunctionOverloadSetsBySimpleName(name)
        }
    }
}