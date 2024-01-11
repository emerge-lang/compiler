package compiler.binding

import compiler.binding.type.BoundTypeReference
import compiler.ast.type.TypeMutability

interface ObjectMember {
    val name: String

    /**
     * The type of this member in the context of the hosting data structure. It still needs to
     * be [BoundTypeReference.instantiateAllParameters]-ed with the type of the variable used to access
     * the hosting data structure.
     */
    val type: BoundTypeReference?

    /**
     * Whether the member is inherently mutable. Even if this is `true` it still has to
     * be allowed by the [TypeMutability] of the hosting data structure.
     */
    val isMutable: Boolean
}