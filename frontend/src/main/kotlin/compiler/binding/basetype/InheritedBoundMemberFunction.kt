package compiler.binding.basetype

import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.BoundVariable
import compiler.binding.type.BaseType
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting

class InheritedBoundMemberFunction(
    val supertypeMemberFn: BoundMemberFunction,
    val subtype: BaseType,
) : BoundMemberFunction by supertypeMemberFn {
    init {
        check(supertypeMemberFn.declaresReceiver) {
            "Inheriting a member function without receiver - that's nonsensical!"
        }
    }

    // this is intentional - as long as not overridden, this info is truthful & accurate
    override val declaredOnType get()= supertypeMemberFn.declaredOnType

    override val receiverType: BoundTypeReference get() {
        check(subtype.typeParameters.isEmpty()) {
            "Not supported yet"
        }
        return subtype.baseReference
    }

    override val parameters: BoundParameterList by lazy {
        val inheritedReceiverParameter = supertypeMemberFn.parameters.declaredReceiver!!
        val narrowedReceiverParameter = VariableDeclaration(
            inheritedReceiverParameter.declaration.declaredAt,
            null,
            null,
            inheritedReceiverParameter.declaration.ownership,
            inheritedReceiverParameter.declaration.name,
            TypeReference(subtype.simpleName),
            null,
        )
        val boundNarrowedReceiverParameter = narrowedReceiverParameter.bindTo(inheritedReceiverParameter.context, BoundVariable.Kind.PARAMETER)
        BoundParameterList(
            supertypeMemberFn.parameters.context,
            supertypeMemberFn.parameters.declaration,
            listOf(boundNarrowedReceiverParameter) + (supertypeMemberFn.parameters.parameters.drop(1))
        )
    }

    // semantic analysis not needed here
    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return emptySet()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return emptySet()
    }
}