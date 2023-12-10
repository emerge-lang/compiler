package compiler.binding

import compiler.binding.type.ResolvedTypeReference
import compiler.ast.type.TypeMutability

interface ObjectMember {
    val name: String
    val type: ResolvedTypeReference?

    /**
     * Whether the member is inherently mutable. Even if this is `true` it still has to
     * be allowed by the [TypeMutability] of the hosting data structure.
     */
    val isMutable: Boolean
}