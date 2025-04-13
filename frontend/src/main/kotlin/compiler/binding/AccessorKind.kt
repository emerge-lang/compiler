package compiler.binding

import compiler.binding.type.BoundTypeReference

sealed interface AccessorKind {
    /**
     * The type of the virtual member variable defined by this accessor, as defined in the accessor declaration.
     */
    fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference?

    data object Read : AccessorKind {
        override fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference? {
            return accessorFnOfKind.returnType
        }
    }

    data object Write : AccessorKind {
        override fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference? {
            return accessorFnOfKind.parameters.parameters
                .drop(1)
                .firstOrNull()
                ?.typeAtDeclarationTime
        }
    }
}