/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding.context

import compiler.InternalCompilerError
import compiler.ast.Bindable
import compiler.ast.FunctionDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import java.util.*

/**
 * Mutable compile-time context; for explanation, see the doc of [CTContext].
 */
open class MutableCTContext(
    /**
     * The context this one is derived off of
     */
    override val parentContext: CTContext = CTContext.EMPTY
) : CTContext
{
    private val imports: MutableSet<ImportDeclaration> = HashSet()

    private val hierarchy by lazy {
        val hierarchy = ArrayList<CTContext>(10)
        var _context: CTContext? = this
        while (_context != null) {
            hierarchy.add(_context!!)
            _context = _context!!.parentContext
        }

        hierarchy
    }

    override var swCtx: SoftwareContext? = null
        get() = field ?: parentContext.swCtx
        set(ctx) { field = ctx }

    override var module: Module? = null
        get() = field ?: parentContext.module
        set(module) { field = module }

    /** Maps variable names to their metadata; holds only variables defined in this context */
    private val variablesMap: MutableMap<String, BoundVariable> = HashMap()

    override val variables
        get() = variablesMap.values

    /** Holds all the toplevel functions defined in this context */
    override val functions: MutableSet<BoundFunction> = HashSet()

    /** Holds all the base types defined in this context */
    private val types: MutableSet<BaseType> = HashSet()

    fun addImport(decl: ImportDeclaration) {
        this.imports.add(decl)
    }

    /**
     * Adds the given [BaseType] to this context, possibly overriding
     */
    open fun addBaseType(type: BaseType) {
        types.add(type)
    }

    override fun resolveDefinedType(simpleName: String): BaseType? = types.find { it.simpleName == simpleName }

    override fun resolveAnyType(ref: TypeReference): BaseType? {
        if (ref is BaseTypeReference) return ref.baseType

        if (ref.declaredName.contains('.')) {
            val swCtx = this.swCtx ?: throw InternalCompilerError("Cannot resolve FQN when no software context is set.")

            // FQN specified
            val fqnName = ref.declaredName.split('.')
            val simpleName = fqnName.last()
            val moduleNameOfType = fqnName.dropLast(1)
            val foreignModuleCtx = swCtx.module(moduleNameOfType)
            return foreignModuleCtx?.context?.resolveDefinedType(simpleName)
        }
        else {
            // try to resolve from this context
            val selfDefined = resolveDefinedType(ref.declaredName)
            if (selfDefined != null) return selfDefined

            // look through the imports
            val importedTypes = importsForSimpleName(ref.declaredName)
                .map { it.resolveDefinedType(ref.declaredName) }
                .filterNotNull()

            // TODO: if importedTypes.size is > 1 the reference is ambigous; how to handle that?
            return importedTypes.firstOrNull() ?: parentContext.resolveAnyType(ref)
        }
    }

    /**
     * Adds the given variable to this context; possibly overriding its type with the given type.
     */
    open fun addVariable(declaration: Bindable<BoundVariable>): BoundVariable {
        val bound = declaration.bindTo(this)

        return addVariable(bound)
    }

    open fun addVariable(boundVariable: BoundVariable): BoundVariable {
        if (boundVariable.context in hierarchy) {
            variablesMap[boundVariable.name] = boundVariable
            return boundVariable
        }

        throw InternalCompilerError("Cannot add a variable that has been bound to a different context")
    }

    override fun resolveVariable(name: String, onlyOwn: Boolean): BoundVariable? {
        val ownVar = variablesMap[name]
        if (onlyOwn || ownVar != null) return ownVar

        val importedVars = importsForSimpleName(name)
            .map { it.resolveVariable(name, true) }
            .filterNotNull()

        // TODO: if importedVars.size is > 1 the name is ambigous; how to handle that?
        return importedVars.firstOrNull() ?: parentContext.resolveVariable(name, onlyOwn)
    }

    override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean {
        if (variablesMap.containsValue(variable)) return true

        if (this !== boundary) {
            if (parentContext == CTContext.EMPTY) {
                // the boundary is not in the hierarchy => error
                throw InternalCompilerError("The given boundary is not part of the hierarchy of the invoked context")
            }

            return parentContext.containsWithinBoundary(variable, boundary)
        }

        return false
    }

    open fun addFunction(declaration: FunctionDeclaration): BoundFunction {
        val bound = declaration.bindTo(this)
        functions.add(bound)
        return bound
    }

    override fun resolveDefinedFunctions(name: String): Collection<BoundFunction> = functions.filter { it.declaration.name.value == name }

    override fun resolveAnyFunctions(name: String): Collection<BoundFunction> {
        if (name.contains('.')) {
            val swCtx = this.swCtx ?: throw InternalCompilerError("Cannot resolve FQN when no software context is set.")

            // FQN specified
            val fqnName = name.split('.')
            val simpleName = fqnName.last()
            val moduleNameOfType = fqnName.dropLast(1)
            val foreignModuleCtx = swCtx.module(moduleNameOfType)
            return foreignModuleCtx?.context?.resolveDefinedFunctions(simpleName) ?: emptySet()
        }
        else {
            // try to resolve from this context
            val selfDefined = resolveDefinedFunctions(name)

            // look through the imports
            val importedTypes = importsForSimpleName(name)
                .map { it.resolveDefinedFunctions(name) }
                .filterNotNull()

            // TODO: if importedTypes.size is > 1 the reference is ambiguous; how to handle that?
            return selfDefined + (importedTypes.firstOrNull() ?: emptySet()) + parentContext.resolveAnyFunctions(name)
        }
    }

    /**
     * @return All the imported contexts that could contain the given simple name.
     */
    private fun importsForSimpleName(simpleName: String): Iterable<CTContext> {
        val swCtx = this.swCtx ?: throw InternalCompilerError("Cannot resolve symbol $simpleName including imports when no software context is set.")

        return imports.map { import ->
            val importRange = import.identifiers.map(IdentifierToken::value)
            val moduleName = importRange.dropLast(1)
            val importSimpleName = importRange.last()

            if (importSimpleName != "*" && importSimpleName != simpleName) {
                return@map null
            }

            return@map swCtx.module(moduleName)?.context
        }
            .filterNotNull()
    }

    companion object {
        /**
         * Derives a new [MutableCTContext] from the given one, runs `initFn` on it and returns it.
         */
        fun deriveFrom(context: CTContext, initFn: MutableCTContext.() -> Any? = {}): MutableCTContext {
            val newContext = MutableCTContext(context)
            newContext.swCtx = context.swCtx

            newContext.initFn()

            return newContext
        }
    }
}

private fun <T, R> Iterable<T>.firstNotNull(transform: (T) -> R?): R? = map(transform).filterNot{ it == null }.firstOrNull()