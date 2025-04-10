package compiler.binding.basetype

import compiler.ast.BaseTypeMemberVariableAccessorDeclaration
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.BoundDeclaredFunction
import compiler.binding.BoundFunctionAttributeList
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.lexer.IdentifierToken
import compiler.lexer.Span
import compiler.lexer.Token
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundBaseTypeMemberVariableAccessor(
    val declaration: BaseTypeMemberVariableAccessorDeclaration,
    private val getMemberVar: () -> BoundBaseTypeMemberVariable,
    override val attributes: BoundFunctionAttributeList,
    val accessType: AccessType,
    override val parameters: BoundParameterList,
    val body: BoundDeclaredFunction.Body?,
) : BoundMemberFunction {
    override val declaredOnType get() =  getMemberVar().
    override val ownerBaseType: BoundBaseType
        get() = TODO("Not yet implemented")
    override val isVirtual: Boolean
        get() = TODO("Not yet implemented")
    override val isAbstract: Boolean
        get() = TODO("Not yet implemented")
    override val overrides: Set<InheritedBoundMemberFunction>?
        get() = TODO("Not yet implemented")

    override fun toBackendIr(): IrMemberFunction {
        TODO("Not yet implemented")
    }

    override val context: CTContext
        get() = TODO("Not yet implemented")
    override val declaredAt: Span
        get() = TODO("Not yet implemented")
    override val receiverType: BoundTypeReference?
        get() = TODO("Not yet implemented")
    override val declaresReceiver: Boolean
        get() = TODO("Not yet implemented")
    override val name: String
        get() = TODO("Not yet implemented")
    override val allTypeParameters: List<BoundTypeParameter>
        get() = TODO("Not yet implemented")
    override val declaredTypeParameters: List<BoundTypeParameter>
        get() = TODO("Not yet implemented")
    override val throwBehavior: SideEffectPrediction?
        get() = TODO("Not yet implemented")
    override val returnType: BoundTypeReference?
        get() = TODO("Not yet implemented")
    override val canonicalName: CanonicalElementName.Function
        get() = TODO("Not yet implemented")

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        TODO("Not yet implemented")
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        TODO("Not yet implemented")
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        TODO("Not yet implemented")
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        TODO("Not yet implemented")
    }

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