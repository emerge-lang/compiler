package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.struct.Struct
import compiler.binding.type.BaseType

class ModuleRootContext : MutableCTContext(
    EMPTY,
) {
    override lateinit var swCtx: SoftwareContext
    override lateinit var module: Module

    val variables: Collection<BoundVariable> = _variables.values
    val functions: Collection<BoundFunction> = _functions
    val structs: Collection<Struct> = _structs
    val types: Collection<BaseType> = _types

    private companion object {
        val EMPTY = object : CTContext {
            override val swCtx: SoftwareContext
                get() = throw InternalCompilerError("${SoftwareContext::class.simpleName} not initialized yet")

            override val module: Module
                get() = throw InternalCompilerError("module not initialized yet")

            override fun resolveVariable(name: String, fromOwnModuleOnly: Boolean): BoundVariable? = null
            override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean = false
            override fun resolveType(ref: TypeReference, fromOwnModuleOnly: Boolean): BaseType? = null
            override fun resolveFunction(name: String, fromOwnModuleOnly: Boolean): Collection<BoundFunction> = emptySet()
        }
    }
}