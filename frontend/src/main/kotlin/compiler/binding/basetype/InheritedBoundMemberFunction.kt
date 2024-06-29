package compiler.binding.basetype

import compiler.ast.VariableDeclaration
import compiler.ast.type.NamedTypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameter
import compiler.binding.BoundParameterList
import compiler.binding.BoundVariable
import compiler.binding.type.BoundTypeReference
import compiler.lexer.IdentifierToken
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrFullyInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction

class InheritedBoundMemberFunction(
    val supertypeMemberFn: BoundMemberFunction,
    val subtype: BoundBaseType,
) : BoundMemberFunction by supertypeMemberFn {
    init {
        check(supertypeMemberFn.declaresReceiver) {
            "Inheriting a member function without receiver - that's nonsensical!"
        }
    }

    // this is intentional - as long as not overridden, this info is truthful & accurate
    override val declaredOnType get()= supertypeMemberFn.declaredOnType

    override val receiverType: BoundTypeReference get() {
        check(subtype.typeParameters.isNullOrEmpty()) {
            "Not supported yet"
        }
        return subtype.baseReference
    }

    private val boundNarrowedReceiverParameter: BoundParameter = run {
        val inheritedReceiverParameter = supertypeMemberFn.parameters.declaredReceiver!!
        val sourceLocation = inheritedReceiverParameter.declaration.declaredAt.deriveGenerated()
        val narrowedReceiverParameter = VariableDeclaration(
            sourceLocation,
            null,
            null,
            inheritedReceiverParameter.declaration.ownership,
            inheritedReceiverParameter.declaration.name,
            NamedTypeReference(subtype.simpleName, declaringNameToken = IdentifierToken(subtype.simpleName, sourceLocation)),
            null,
        )
        narrowedReceiverParameter.bindTo(inheritedReceiverParameter.context, BoundVariable.Kind.PARAMETER)
    }

    override val parameters: BoundParameterList = run {
        BoundParameterList(
            supertypeMemberFn.parameters.context,
            supertypeMemberFn.parameters.declaration,
            listOf(boundNarrowedReceiverParameter) + (supertypeMemberFn.parameters.parameters.drop(1))
        )
    }

    override val parameterTypes get() = super.parameterTypes

    // semantic analysis not needed here
    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        check(boundNarrowedReceiverParameter.semanticAnalysisPhase1().isEmpty())
        return emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        check(boundNarrowedReceiverParameter.semanticAnalysisPhase2().isEmpty())
        return emptySet()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        check(boundNarrowedReceiverParameter.semanticAnalysisPhase3().isEmpty())
        return emptySet()
    }

    private val backendIr by lazy {
        IrFullyInheritedMemberFunctionImpl(supertypeMemberFn.toBackendIr())
    }
    override fun toBackendIr(): IrMemberFunction = backendIr

    override fun toString(): String {
        return "$canonicalName(${parameters.parameters.joinToString(separator = ", ", transform = { it.typeAtDeclarationTime.toString() })}) -> $returnType"
    }
}

private class IrFullyInheritedMemberFunctionImpl(
    override val superFunction: IrMemberFunction
) : IrFullyInheritedMemberFunction, IrMemberFunction by superFunction