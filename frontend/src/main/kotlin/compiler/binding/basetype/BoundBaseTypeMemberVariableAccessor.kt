package compiler.binding.basetype

import compiler.ast.BaseTypeMemberVariableAccessorDeclaration
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.lexer.IdentifierToken
import compiler.lexer.Token

class BoundBaseTypeMemberVariableAccessor(
    val declaration: BaseTypeMemberVariableAccessorDeclaration,
    private val getMemberVar: () -> BoundBaseTypeMemberVariable,
    override val attributes: BoundFunctionAttributeList,
    val accessType: AccessType,
    override val parameters: BoundParameterList,
    val body: BoundDeclaredFunction.Body?,
) : BoundMemberFunction {
    enum class AccessType {
        READ,
        WRITE,
        ;

        fun buildDefaultParams(accessorKeywordToken: Token, memberType: TypeReference): ParameterList {
            val selfParam = VariableDeclaration(
                accessorKeywordToken.span,
                null,
                null,
                null,
                IdentifierToken("self", accessorKeywordToken.span),
                null,
                null,
            )
            return when (this) {
                READ -> ParameterList(listOf(selfParam))
                WRITE -> ParameterList(listOf(
                    selfParam,
                    VariableDeclaration(
                        accessorKeywordToken.span,
                        null,
                        null,
                        null,
                        IdentifierToken("value", accessorKeywordToken.span),
                        memberType,
                        null,
                    )
                ))
            }
        }
    }
}