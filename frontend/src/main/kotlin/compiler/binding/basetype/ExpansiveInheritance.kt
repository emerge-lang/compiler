package compiler.binding.basetype

import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import java.util.IdentityHashMap

/**
 * Inheritance is expansive where a type parameter recurs, nested deeper, in the supertypes of its own type, as in
 * `interface N<Z> : C<N<N<Z>>>`: infinitely many types are reachable through the supertypes of `N<X>` then, and
 * checking subtyping may go on forever (Kennedy and Pierce, "On Decidability of Nominal Subtyping with Variance").
 *
 * In a graph of the type parameters, there is an edge from `X` to the j-th type parameter of `G` wherever `X` is the
 * j-th type argument of a `G<...>` in a supertype declaration; an expansive one where `X` is nested deeper in it.
 * Inheritance is expansive where a cycle has an expansive edge.
 *
 * @return the supertype declarations that make for an expansive edge in a cycle
 */
fun findExpansiveSupertypes(baseTypes: Iterable<BoundBaseType>): Set<BoundSupertypeDeclaration> {
    val edges = IdentityHashMap<BoundTypeParameter, MutableList<Edge>>()
    for (baseType in baseTypes) {
        for (supertype in baseType.superTypes.clauses) {
            val reference = supertype.resolvedReference ?: continue
            forEachConstructedType(reference) { constructed ->
                val parameters = constructed.baseType.typeParameters ?: return@forEachConstructedType
                val arguments = constructed.arguments ?: return@forEachConstructedType
                parameters.zip(arguments).forEach { (parameter, argument) ->
                    forEachTypeParameterIn(argument, nested = false) { from, nested ->
                        edges.getOrPut(from, ::ArrayList).add(Edge(parameter, nested, supertype))
                    }
                }
            }
        }
    }

    return edges.entries
        .flatMap { (from, outgoing) -> outgoing.filter { it.expansive && reaches(edges, it.to, from) } }
        .mapTo(HashSet()) { it.declaredIn }
}

private class Edge(val to: BoundTypeParameter, val expansive: Boolean, val declaredIn: BoundSupertypeDeclaration)

private fun reaches(edges: IdentityHashMap<BoundTypeParameter, MutableList<Edge>>, from: BoundTypeParameter, to: BoundTypeParameter): Boolean {
    val visited = IdentityHashMap<BoundTypeParameter, Unit>()
    val pending = ArrayDeque(listOf(from))
    while (pending.isNotEmpty()) {
        val current = pending.removeFirst()
        if (current === to) {
            return true
        }
        if (visited.put(current, Unit) != null) {
            continue
        }
        edges[current]?.forEach { pending.add(it.to) }
    }
    return false
}

private fun forEachConstructedType(type: BoundTypeReference, action: (RootResolvedTypeReference) -> Unit) {
    when (type) {
        is RootResolvedTypeReference -> {
            action(type)
            type.arguments?.forEach { forEachConstructedType(it, action) }
        }
        is BoundTypeArgument -> forEachConstructedType(type.type, action)
        is NullableTypeReference -> forEachConstructedType(type.nested, action)
        is BoundIntersectionTypeReference -> type.components.forEach { forEachConstructedType(it, action) }
        else -> {}
    }
}

private fun forEachTypeParameterIn(type: BoundTypeReference, nested: Boolean, action: (BoundTypeParameter, Boolean) -> Unit) {
    when (type) {
        is GenericTypeReference -> action(type.parameter, nested)
        is RootResolvedTypeReference -> type.arguments?.forEach { forEachTypeParameterIn(it, true, action) }
        is BoundTypeArgument -> forEachTypeParameterIn(type.type, nested, action)
        is NullableTypeReference -> forEachTypeParameterIn(type.nested, nested, action)
        is BoundIntersectionTypeReference -> type.components.forEach { forEachTypeParameterIn(it, nested, action) }
        else -> {}
    }
}
