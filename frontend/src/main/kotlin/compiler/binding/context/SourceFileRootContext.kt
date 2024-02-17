package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.struct.Struct
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.UnresolvedType

class SourceFileRootContext(
    val packageContext: PackageContext,
) : MutableCTContext(
    SourceFileParentContext(packageContext),
) {
    override var moduleContext: ModuleContext = packageContext.moduleContext
    override lateinit var sourceFile: SourceFile

    val variables: Collection<BoundVariable> = _variables.values
    val functions: Collection<BoundFunction> = _functions
    val structs: Collection<Struct> = _structs
    val types: Collection<BaseType> = _types

    private companion object {
        val EMPTY = object : CTContext {
            override val swCtx: SoftwareContext
                get() = throw InternalCompilerError("${this::swCtx.name} not initialized yet")

            override val moduleContext: ModuleContext
                get() = throw InternalCompilerError("${this::moduleContext.name} not initialized yet")

            override val sourceFile: SourceFile
                get() = throw InternalCompilerError("file not initialized yet")

            override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? = null
            override fun initializesVariable(variable: BoundVariable): Boolean = false
            override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean = false
            override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? = null
            override fun resolveBaseType(simpleName: String, fromOwnFileOnly: Boolean): BaseType? = null
            override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference = UnresolvedType(
                ref,
                ref.arguments.map { BoundTypeArgument(it, it.variance, this.resolveType(it.type)) },
            )
            override fun resolveFunction(name: String, fromOwnFileOnly: Boolean): Collection<BoundFunction> = emptySet()
        }
    }

    private class SourceFileParentContext(val packageContext: PackageContext) : CTContext by EMPTY {
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

        override fun resolveFunction(name: String, fromOwnFileOnly: Boolean): Collection<BoundFunction> {
            if (fromOwnFileOnly) {
                return EMPTY.resolveFunction(name, fromOwnFileOnly)
            }

            return packageContext.resolveFunction(name)
        }
    }
}