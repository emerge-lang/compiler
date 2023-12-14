package compiler.binding.type

class TypesNotUnifiableException(
    val left: ResolvedTypeReference,
    val right: ResolvedTypeReference,
    val reason: String
) : RuntimeException("Type $left cannot be unified with $right: $reason")