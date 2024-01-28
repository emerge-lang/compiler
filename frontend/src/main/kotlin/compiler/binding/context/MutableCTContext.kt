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
import compiler.ast.struct.StructDeclaration
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.struct.Struct
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.UnresolvedType
import compiler.lexer.IdentifierToken

/**
 * Mutable compile-time context; for explanation, see the doc of [CTContext].
 */
open class MutableCTContext(
    /**
     * The context this one is derived off of
     */
    private val parentContext: CTContext,
) : CTContext {
    private val imports: MutableSet<ImportDeclaration> = HashSet()

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

    private val hierarchy: Sequence<CTContext> = generateSequence(this as CTContext) { (it as? MutableCTContext)?.parentContext }

    /** Maps variable names to their metadata; holds only variables defined in this context */
    protected val _variables: MutableMap<String, BoundVariable> = HashMap()

    /** Holds all the toplevel functions defined in this context */
    protected val _functions: MutableSet<BoundFunction> = HashSet()

    /** Holds all the toplevel structs defined in this context */
    protected val _structs: MutableSet<Struct> = HashSet()

    /** Holds all the base types defined in this context */
    protected val _types: MutableSet<BaseType> = HashSet()

    fun addImport(decl: ImportDeclaration) {
        this.imports.add(decl)
    }

    /**
     * Adds the given [BaseType] to this context, possibly overriding
     */
    open fun addBaseType(type: BaseType) {
        _types.add(type)
        if (type is Struct) _structs.add(type)
    }

    open fun addStruct(definition: StructDeclaration): Struct {
        val bound = definition.bindTo(this)
        _types.add(bound)
        _structs.add(bound)
        return bound
    }

    private val typeParameters = HashMap<String, BoundTypeParameter>()

    open fun addTypeParameter(parameter: TypeParameter): BoundTypeParameter {
        check(parameter.name.value !in typeParameters) {
            "Duplicate type parameter in context: $parameter"
        }
        val bound = parameter.bindTo(this)
        typeParameters[parameter.name.value] = bound
        return bound
    }

    override fun resolveTypeParameter(simpleName: String): BoundTypeParameter? {
        return typeParameters[simpleName] ?: parentContext.resolveTypeParameter(simpleName)
    }

    override fun resolveBaseType(simpleName: String, fromOwnFileOnly: Boolean): BaseType? {
        _types.find { it.simpleName == simpleName }?.let { return it }

        val fromImport = if (fromOwnFileOnly) null else {
            val importedTypes = importsForSimpleName(simpleName)
                .mapNotNull { it.resolveBaseType(simpleName) }

            // TODO: if importedTypes.size is > 1 the reference is ambiguous; how to handle that?
            importedTypes.firstOrNull()
        }

        return fromImport ?: parentContext.resolveBaseType(simpleName, fromOwnFileOnly)
    }

    override fun resolveType(ref: TypeArgument): BoundTypeArgument {
        return BoundTypeArgument(ref, ref.variance, resolveType(ref.type))
    }

    override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference {
        resolveTypeParameter(ref.simpleName)?.let { parameter ->
            return GenericTypeReference(ref, parameter)
        }

        val resolvedParameters = ref.arguments.map { resolveType(it).defaultMutabilityTo(ref.mutability) }
        return resolveBaseType(ref.simpleName)
            ?.let { RootResolvedTypeReference(ref, it, resolvedParameters) }
            ?: UnresolvedType(ref, resolvedParameters)
    }

    override fun resolveVariable(name: String, fromOwnFileOnly: Boolean): BoundVariable? {
        _variables[name]?.let { return it }

        val fromImport = if (fromOwnFileOnly) null else {
            val importedVars = importsForSimpleName(name)
                .mapNotNull { it.resolveVariable(name) }

            // TODO: if importedVars.size is > 1 the name is ambiguous; how to handle that?
            importedVars.firstOrNull()
        }

        return fromImport ?: parentContext.resolveVariable(name, fromOwnFileOnly)
    }

    override fun containsWithinBoundary(variable: BoundVariable, boundary: CTContext): Boolean {
        if (_variables.containsValue(variable)) return true

        if (this === boundary) {
            return false
        }

        return parentContext.containsWithinBoundary(variable, boundary)
    }

    open fun addFunction(declaration: FunctionDeclaration): BoundFunction {
        val bound = declaration.bindTo(this)
        _functions.add(bound)
        return bound
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
            _variables[boundVariable.name] = boundVariable
            return boundVariable
        }

        throw InternalCompilerError("Cannot add a variable that has been bound to a different context")
    }

    override fun resolveFunction(name: String, fromOwnFileOnly: Boolean): Collection<BoundFunction> {
        // try to resolve from this context
        val selfDefined = _functions.filter { it.name == name }

        // look through the imports
        val importedTypes = if (fromOwnFileOnly) emptySet() else {
            importsForSimpleName(name)
                .map { it.resolveFunction(name) }
                .flatten()
        }

        return (selfDefined + importedTypes + parentContext.resolveFunction(name, fromOwnFileOnly)).toSet()
    }

    /**
     * @return All the imported contexts that could contain the given simple name.
     */
    private fun importsForSimpleName(simpleName: String): Iterable<PackageContext> {
        return imports.mapNotNull { import ->
            val importRange = import.identifiers.map(IdentifierToken::value)
            val packageName = importRange.dropLast(1)
            val importSimpleName = importRange.last()

            if (importSimpleName != "*" && importSimpleName != simpleName) {
                return@mapNotNull null
            }

            return@mapNotNull swCtx.getPackage(packageName)
        }
    }
}