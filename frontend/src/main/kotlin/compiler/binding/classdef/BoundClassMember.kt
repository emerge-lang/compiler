package compiler.binding.classdef

import compiler.binding.SemanticallyAnalyzable
import compiler.binding.type.BoundTypeReference

sealed interface BoundClassMember : BoundClassEntry, SemanticallyAnalyzable {
    val name: String

    /**
     * The type of this member in the context of the hosting data structure. It still needs to
     * be [BoundTypeReference.instantiateAllParameters]-ed with the type of the variable used to access
     * the hosting data structure.
     */
    val type: BoundTypeReference?
}