package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.Statement
import compiler.ast.type.TypeReference
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.UnresolvedType

class SourceFileRootContext(
    packageContext: PackageContext,
) : MutableExecutionScopedCTContext(
    SourceFileParentContext(packageContext),
    true,
    false,
) {
    override lateinit var sourceFile: SourceFile

    val variables: Collection<BoundVariable> = _variables.values
    val functions: Collection<BoundFunction> = _functions
    val classes: Collection<BoundClassDefinition> = _classes
    val types: Collection<BaseType> = _types

    override fun addDeferredCode(code: Statement) {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getContextLocalDeferredCode(): Sequence<BoundExecutable<*>> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getScopeLocalDeferredCode(): Sequence<BoundExecutable<*>> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    override fun getFunctionDeferredCode(): Sequence<BoundExecutable<*>> {
        throw InternalCompilerError("Deferred code on source-file level is currently not possible. Maybe implement as global destructors in the future?")
    }

    private companion object {
        val EMPTY = object : ExecutionScopedCTContext {
            override val swCtx: SoftwareContext
                get() = throw InternalCompilerError("${this::swCtx.name} not initialized yet")

            override val moduleContext: ModuleContext
                get() = throw InternalCompilerError("${this::moduleContext.name} not initialized yet")

            override val sourceFile: SourceFile
                get() = throw InternalCompilerError("file not initialized yet")

            override val isScopeBoundary = false
            override val isFunctionRoot = false
            override val imports = emptySet<BoundImportDeclaration>()

            override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? = null
            override fun initializesVariable(variable: BoundVariable): Boolean = false
            override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean = false
            override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? = null
            override fun resolveBaseType(simpleName: String, fromOwnFileOnly: Boolean): BaseType? = null
            override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference = UnresolvedType(
                ref,
                ref.arguments.map { BoundTypeArgument(it, it.variance, this.resolveType(it.type)) },
            )
            override fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet> = emptySet()

            override fun getContextLocalDeferredCode(): Sequence<BoundExecutable<*>> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getScopeLocalDeferredCode(): Sequence<BoundExecutable<*>> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
            override fun getFunctionDeferredCode(): Sequence<BoundExecutable<*>> {
                throw InternalCompilerError("Should be implemented on the level of ${SourceFileRootContext::class.qualifiedName}")
            }
        }
    }

    private class SourceFileParentContext(val packageContext: PackageContext) : ExecutionScopedCTContext by EMPTY {
        override val moduleContext = packageContext.moduleContext

        override val sourceFile: SourceFile
            get() = throw InternalCompilerError("shouldn't be accessed")

        override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
            if (fromOwnFileOnly) {
                return EMPTY.resolveVariable(name, fromOwnFileOnly)
            }

            return packageContext.resolveVariable(name)
        }

        override fun resolveBaseType(simpleName: String, fromOwnFileOnly: Boolean): BaseType? {
            if (fromOwnFileOnly) {
                return EMPTY.resolveBaseType(simpleName, fromOwnFileOnly)
            }

            return packageContext.resolveBaseType(simpleName)
        }

        override fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet> {
            return packageContext.getTopLevelFunctionOverloadSetsBySimpleName(name)
        }
    }
}