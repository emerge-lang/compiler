package compiler.binding.type

class TypesNotUnifiableException(
    val left: BoundTypeReference,
    val right: BoundTypeReference,
    val reason: String
) : RuntimeException("Type $left cannot be unified with $right: $reason")