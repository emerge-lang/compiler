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
    EMPTY,
) {
    override var moduleContext: ModuleContext = packageContext.module
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
}