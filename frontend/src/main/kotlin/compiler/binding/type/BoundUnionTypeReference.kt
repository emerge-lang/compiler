package compiler.binding.type

import compiler.ast.type.AstUnionType

class BoundUnionTypeReference(
    val astNode: AstUnionType,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {

}