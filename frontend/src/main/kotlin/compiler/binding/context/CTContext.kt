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

import compiler.ast.type.*
import compiler.binding.BoundImportDeclaration
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.effect.EphemeralStateClass
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.TypeUnification
import compiler.binding.type.BoundTypeReference
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

/**
 * Compile-Time context. A compile-time context knows all available symbols (through imports and explicit definition).
 * Contexts in which order of symbol declaration is irrelevant are mutable, contexts in which the order of declaration
 * *is* relevant are immutable. Contexts that mix these two parts are implemented by referring to a mutable context from
 * an immutable one (e.g. immutable context within function code refers to mutable context of the enclosing class/file).
 *
 * Consider this example (mutable, file level)
 *
 *     // mutable context A
 *     val x = 3 + y // x is added to A, A is mutated
 *     val y = 3     // y is added to A, A is mutated
 *
 * When x has to be evaluated, y is present because order of declaration is not important on file level.
 *
 * Another example (function scope, immutable):
 *
 *     fun fn(e: Int, f: Int) {
 *         // the immutable context A is initialized with e and f
 *         val g = e + f // a new context B is derived from A with g added to it
 *         val h = g + 1 // OK, h is evaluated in context B in which g is present
 *                       // context C is derived from B with h added to it
 *         val i = k + 1 // ERROR when evaluating i because k is not defined in context C
 *         val k = f + 1
 *     }
 *
 * The naming for (im)mutable context is coherent with Kotlin collections: CTContext is immutable, MutableCTContext
 * is mutable.
 * All contexts in use are [MutableCTContext]s; this interface contains only the immutable operations. It is used
 * to convey that the context must not be modified to assure correct compilation, CTFE or interpretation. Much like
 * the `immutable` keyword in Emerge.
 */
interface CTContext {
    val swCtx: SoftwareContext get() = moduleContext.softwareContext

    val moduleContext: ModuleContext

    val packageName: CanonicalElementName.Package

    /** The file this context belongs to, right beneath the module context in the tree */
    val sourceFile: SourceFile

    val imports: Iterable<BoundImportDeclaration>

    /**
     * E.g. when inside a class context, this is the visibility of the class
     */
    val visibility: BoundVisibility

    fun resolveBaseType(simpleName: String): Sequence<BoundBaseType>

    /**
     * @return whether this context has a [BoundImportDeclaration] that refers to [simpleName] (or is a import-all)
     * and that is erroneous (no symbol for [simpleName] found or package not found).
     */
    fun hasUnresolvableImportForSimpleName(simpleName: String): Boolean

    /**
     * @return whether resolving [simpleName] in this context is ambiguous simply due to the imports
     * (if so, the fault is in the import, and references just suffer along).
     */
    fun hasAmbiguousImportOrDeclarationsForSimpleName(simpleName: String): Boolean

    fun resolveTypeParameter(simpleName: String): BoundTypeParameter?

    val allTypeParameters: Sequence<BoundTypeParameter>

    /**
     * Resolves a type argument for which there is no type parameter to look at: a wildcard is `out Any?` then.
     * For the type arguments of a base type, see [resolveTypeArguments].
     */
    fun resolveTypeArgument(ref: AstTypeArgument): BoundTypeArgument {
        return when (ref) {
            is AstSpecificTypeArgument -> BoundTypeArgument(this, ref, ref.variance, resolveType(ref.type))
            is AstWildcardTypeArgument -> BoundTypeArgument(this, ref, TypeVariance.OUT, swCtx.getTopType(ref.span ?: Span.UNKNOWN))
        }
    }

    /**
     * Resolves the type arguments [refs] for the type parameters [parameters] of a base type.
     *
     * A wildcard (`*`) is the star projection of Kotlin: `out B`, where `B` is the bound of the parameter as the
     * other type arguments make it. Given `class Sorted<T, C : Comparator<T>>`, `Sorted<String, *>` is
     * `Sorted<String, out Comparator<String>>`. Where a bound mentions its own parameter (`T : Comparable<T>`),
     * that is all there is to say about the type in its place: it is `out Any?` there, so `*` is
     * `out Comparable<out Any?>`.
     *
     * @param parameters `null` if the base type is not known; wildcards are `out Any?` then
     */
    fun resolveTypeArguments(refs: List<AstTypeArgument>, parameters: List<BoundTypeParameter>?): List<BoundTypeArgument> {
        fun unknown(ref: AstTypeArgument) = BoundTypeArgument(this, ref, TypeVariance.OUT, swCtx.getTopType(ref.span ?: Span.UNKNOWN))

        val arguments = refs.mapTo(ArrayList(refs.size)) { ref ->
            if (ref is AstWildcardTypeArgument) unknown(ref) else resolveTypeArgument(ref)
        }
        val wildcardIndices = refs.indices.filter { index ->
            // a bound that is being resolved cannot be asked for (`class Foo<T : Foo<*>>`); the wildcard stays `out Any?` there
            refs[index] is AstWildcardTypeArgument && parameters?.getOrNull(index)?.isResolvingBound == false
        }
        if (parameters == null || wildcardIndices.isEmpty()) {
            return arguments
        }

        // in the order of the parameters: a bound mentions only its own parameter and the ones before it, so the
        // wildcards it depends on are done
        for (index in wildcardIndices) {
            val ref = refs[index]
            val bindings = arguments.toMutableList()
            while (bindings.size < parameters.size) {
                bindings.add(unknown(ref))
            }
            val instantiatedBound = BoundTypeArgument(this, ref, TypeVariance.OUT, parameters[index].bound)
                .instantiateAllParameters(TypeUnification.fromExplicit(parameters, parameters, bindings, ref.span ?: Span.UNKNOWN))
            arguments[index] = BoundTypeArgument(this, ref, TypeVariance.OUT, instantiatedBound.type)
        }

        return arguments
    }

    fun resolveType(ref: TypeReference): BoundTypeReference

    /**
     * @return first: the variable accessible under the given name
     */
    fun resolveVariable(name: String, fromOwnFileOnly: Boolean = false): BoundVariable?

    /**
     * @return a variable name that is guaranteed to not be occupied ([resolveVariable] will return `null`),
     * contains markers as an internal variable (prefix of `__`) and contains [namePayload]. Source code cannot
     * use identifiers with that prefix (see [compiler.diagnostic.ReservedIdentifierDiagnostic]), so it cannot refer
     * to the variable either.
     */
    fun findInternalVariableName(namePayload: String): String {
        var i = 0
        var name: String
        do {
            name = "${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX}${namePayload}$i"
            i++
        } while (resolveVariable(name) != null)

        return name
    }

    /**
     * @return a type parameter name that is guaranteed to not be occupied ([resolveTypeParameter] and [resolveBaseType] will return `null`),
     * contains markers as an internal variable (prefix of `__`) and contains [namePayload]. Source code cannot
     * use identifiers with that prefix (see [compiler.diagnostic.ReservedIdentifierDiagnostic]), so it cannot refer
     * to the type parameter either.
     */
    fun findInternalTypeParameterName(namePayload: String): String {
        var i = 0
        var name: String
        do {
            name = "${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX}${namePayload}$i"
            i++
        } while (resolveTypeParameter(name) != null || resolveBaseType(name).any())

        return name
    }

    fun <Subject : Any, State> getEphemeralState(stateClass: EphemeralStateClass<Subject, State, *>, subject: Subject): State {
        return stateClass.getInitialState(subject)
    }

    /**
     * Same as [getEphemeralState], but the state in [ancestor], a direct or indirect parent of `this`, is taken to be
     * [stateInAncestor] instead of computing it again.
     */
    fun <Subject : Any, State> getEphemeralStateRelativeTo(
        ancestor: CTContext,
        stateInAncestor: State,
        stateClass: EphemeralStateClass<Subject, State, *>,
        subject: Subject,
    ): State {
        return if (this === ancestor) stateInAncestor else getEphemeralState(stateClass, subject)
    }

    fun getToplevelFunctionOverloadSetsBySimpleName(name: String): Collection<BoundOverloadSet<*>>
}