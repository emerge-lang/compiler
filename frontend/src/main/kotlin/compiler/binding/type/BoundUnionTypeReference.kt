package compiler.binding.type

import compiler.ast.type.AstUnionType
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.basetype.BoundBaseType
import compiler.lexer.Operator

class BoundUnionTypeReference(
    val astNode: AstUnionType,
    val components: List<BoundTypeReference>,
) : BoundTypeReference {
    override val span = astNode.span
    override val isNullable get()= components.all { it.isNullable }
    override val mutability get()= components.asSequence().map { it.mutability }.reduce(TypeMutability::union)
    override val simpleName get()= components.joinToString(separator = " ${Operator.UNION.text} ", transform = { it.simpleName ?: it.toString() })
    override val baseTypeOfLowerBound by lazy {
        BoundBaseType.closestCommonSupertypeOf(components.map { it.baseTypeOfLowerBound })
    }

    override fun asAstReference(): TypeReference {
        return astNode
    }
}