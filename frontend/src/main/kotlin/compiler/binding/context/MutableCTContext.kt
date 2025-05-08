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
import compiler.ast.BaseTypeDeclaration
import compiler.ast.ImportDeclaration
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.UnresolvedType

/**
 * Mutable compile-time context; for explanation, see the doc of [CTContext].
 */
open class MutableCTContext(
    /**
     * The context this one is derived off of
     */
    internal val parentContext: CTContext,
    overrideVisibility: BoundVisibility? = null
) : CTContext {
    override val visibility: BoundVisibility = overrideVisibility ?: parentContext.visibility

    private val _imports: MutableSet<BoundImportDeclaration> = HashSet()
    override val imports: Iterable<BoundImportDeclaration> = _imports

    private var _moduleContext: ModuleContext? = null
    override var moduleContext: ModuleContext
        get() = _moduleContext ?: parentContext.moduleContext
        set(value) {
            _moduleContext = value
        }

    private var _sourceFile: SourceFile? = null
    override var sourceFile
        get() = _sourceFile ?: parentContext.sourceFile
        set(value) {
            _sourceFile = value
        }

    /** Maps variable names to their metadata; holds only variables defined in this context */
    protected val _variables: MutableMap<String, BoundVariable> = HashMap()

    /** Holds all the toplevel functions defined in this context */
    protected val _functions: MutableSet<BoundDeclaredFunction> = HashSet()

    /** Holds all the base types defined in this context */
    protected val _types: MutableSet<BoundBaseType> = HashSet()

    fun addImport(decl: ImportDeclaration) {
        this._imports.add(decl.bindTo(this))
    }

    /**
     * Adds the given [BoundBaseType] to this context, possibly overriding
     */
    open fun addBaseType(type: BoundBaseType) {
        _types.add(type)
    }

    open fun addBaseType(definition: BaseTypeDeclaration): BoundBaseType {
        val bound = definition.bindTo(this)
        _types.add(bound)
        return bound
    }

    private val typeParameters = LinkedHashMap<String, BoundTypeParameter>()

    open fun addTypeParameter(parameter: BoundTypeParameter) {
        if (typeParameters.putIfAbsent(parameter.name, parameter) != null) {
            throw InternalCompilerError("Duplicate type parameter in context: $parameter")
        }
    }

    override val allTypeParameters: Sequence<BoundTypeParameter>
        get() = parentContext.allTypeParameters + typeParameters.values.asSequence()

    override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? {
        return typeParameters[simpleName] ?: parentContext.resolveTypeParameter(simpleName)
    }

    override fun resolveBaseType(simpleName: String, fromOwnFileOnly: Boolean): BoundBaseType? {
        _types.find { it.simpleName == simpleName }?.let { return it }

        val fromImport = if (fromOwnFileOnly) null else {
            _imports
                .asSequence()
                .mapNotNull { it.getBaseTypeOfName(simpleName) }
                .firstOrNull()
        }

        return fromImport ?: parentContext.resolveBaseType(simpleName, fromOwnFileOnly)
    }

    private fun resolveNamedTypeExceptNullability(ref: NamedTypeReference, fromOwnFileOnly: Boolean): BoundTypeReference {
        resolveTypeParameter(ref.simpleName)?.let { parameter ->
            return GenericTypeReference(ref, parameter)
        }

        val resolvedArguments = ref.arguments?.map(::resolveType)
        return resolveBaseType(ref.simpleName)
            ?.let { RootResolvedTypeReference(this, ref, it, resolvedArguments) }
            ?: UnresolvedType(this, ref, resolvedArguments)
    }

    override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference {
        return when (ref) {
            is AstIntersectionType -> BoundIntersectionTypeReference(this, ref, ref.components.map { this.resolveType(it, fromOwnFileOnly) })
            is NamedTypeReference -> resolveNamedTypeExceptNullability(ref, fromOwnFileOnly).withCombinedNullability(ref.nullability)
        }
    }

    override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
        return parentContext.resolveVariable(name, fromOwnFileOnly)
    }

    fun addFunction(fn: BoundDeclaredFunction) {
        this._functions.add(fn)
    }

    override fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet<*>> {
        val imported = _imports.flatMap { it.getOverloadSetsBySimpleName(name) }
        return imported + parentContext.getToplevelFunctionOverloadSetsBySimpleName(name)
    }
}