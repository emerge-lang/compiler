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
import compiler.ast.AstImportDeclaration
import compiler.ast.BaseTypeDeclaration
import compiler.ast.type.AstAbsoluteTypeReference
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.AstSimpleTypeReference
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
import compiler.binding.type.ErroneousType
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.handleCyclicInvocation

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

    override val packageName get()= parentContext.packageName

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

    fun addImport(decl: AstImportDeclaration) {
        this._imports.add(decl.bindTo(this))
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

    override fun resolveBaseType(simpleName: String): Sequence<BoundBaseType> {
        return handleCyclicInvocation(
            Pair(this, simpleName),
            action = {
                val fromLocal = _types.asSequence().filter { it.simpleName == simpleName }
                val fromImports = _imports.mapNotNull { it.getBaseTypeOfName(simpleName) }
                val fromParent = parentContext.resolveBaseType(simpleName)

                fromLocal + fromParent + fromImports
            },
            onCycle = {
                throw InternalCompilerError("infinite for $simpleName")
            }
        )
    }

    override fun hasUnresolvableImportForSimpleName(simpleName: String): Boolean {
        if (_imports.any { it.isUnresolvedAndAppliesToSimpleName(simpleName) }) {
            return true
        }

        return parentContext.hasUnresolvableImportForSimpleName(simpleName)
    }

    override fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean {
        return parentContext.hasAmbiguousImportOrDeclarationsForSimpleName(simpleName)
    }

    private fun resolveNamedTypeExceptNullability(ref: AstSimpleTypeReference): BoundTypeReference {
        if (ref is NamedTypeReference) {
            resolveTypeParameter(ref.simpleName)?.let { parameter ->
                return GenericTypeReference(ref, parameter)
            }
        }

        val baseTypes = when (ref) {
            is AstAbsoluteTypeReference -> {
                swCtx.getPackage(ref.canonicalTypeName.packageName)
                    ?.resolveBaseType(ref.canonicalTypeName.simpleName)
                    .let(::listOfNotNull)
            }
            is NamedTypeReference -> resolveBaseType(ref.simpleName).distinct().toList()
        }
        val resolvedArguments = ref.arguments?.mapIndexed { index, typeArgAstNode ->
            resolveTypeArgument(typeArgAstNode, baseTypes.singleOrNull()?.typeParameters?.getOrNull(index))
        }

        return baseTypes
            .singleOrNull()
            ?.let { RootResolvedTypeReference(this, ref, it, resolvedArguments) }
            ?: ErroneousType(this, ref, resolvedArguments, baseTypes)
    }

    override fun resolveType(ref: TypeReference): BoundTypeReference {
        return when (ref) {
            is AstIntersectionType -> BoundIntersectionTypeReference.ofComponents(this, ref, ref.components.map(this::resolveType))
            is AstSimpleTypeReference -> resolveNamedTypeExceptNullability(ref).withCombinedNullability(ref.nullability)
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