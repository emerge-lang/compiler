package compiler.binding.basetype

import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.lexer.IdentifierToken
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrFullyInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

class InheritedBoundMemberFunction(
    val supertypeMemberFn: BoundMemberFunction,
    override val ownerBaseType: BoundBaseType,
) : BoundMemberFunction by supertypeMemberFn {
    init {
        check(supertypeMemberFn.declaresReceiver) {
            "Inheriting a member function without receiver - that's nonsensical!"
        }
    }

    private val rawSuperFnContext = supertypeMemberFn.context as? ExecutionScopedCTContext
        ?: MutableExecutionScopedCTContext.functionRootIn(supertypeMemberFn.context)
    override val context = ownerBaseType.context
    private val functionContext = object : ExecutionScopedCTContext by rawSuperFnContext {
        override fun resolveType(ref: TypeReference, fromOwnFileOnly: Boolean): BoundTypeReference {
            if (ref.simpleName == ownerBaseType.simpleName) {
                return ownerBaseType.context.resolveType(ref, fromOwnFileOnly)
            }

            return rawSuperFnContext.resolveType(ref, fromOwnFileOnly)
        }
    }

    override val canonicalName = CanonicalElementName.Function(
        ownerBaseType.canonicalName,
        supertypeMemberFn.name,
    )

    // this is intentional - as long as not overridden, this info is truthful & accurate
    override val declaredOnType get()= supertypeMemberFn.declaredOnType

    override val receiverType: BoundTypeReference get() {
        check(ownerBaseType.typeParameters.isNullOrEmpty()) {
            "Not supported yet"
        }
        return ownerBaseType.baseReference
    }

    private val narrowedReceiverParameter: VariableDeclaration = run {
        check(ownerBaseType.typeParameters.isNullOrEmpty()) {
            "Not supported yet"
        }
        val inheritedReceiverParameter = supertypeMemberFn.parameters.declaredReceiver!!
        // it is important that this location comes from the subtype
        // this is necessary so the access checks pass on module-private or less visible subtypes
        val sourceLocation = ownerBaseType.declaration.declaredAt.deriveGenerated()
        VariableDeclaration(
            sourceLocation,
            null,
            null,
            inheritedReceiverParameter.declaration.ownership,
            inheritedReceiverParameter.declaration.name,
            TypeReference(ownerBaseType.simpleName, declaringNameToken = IdentifierToken(ownerBaseType.simpleName, sourceLocation), mutability = inheritedReceiverParameter.typeAtDeclarationTime?.mutability),
            null,
        )
    }

    override val parameters: BoundParameterList = run {
        ParameterList(
            listOf(narrowedReceiverParameter) + (supertypeMemberFn.parameters.parameters.drop(1).map { it.declaration }),
        ).bindTo(functionContext)
    }

    override val parameterTypes get() = super.parameterTypes

    // semantic analysis is not really needed here; the super function will have its sean functions invoked, too
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        parameters.semanticAnalysisPhase1(diagnosis)
        parameters.parameters.forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase2(diagnosis) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        parameters.parameters.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }

    private val backendIr by lazy {
        IrFullyInheritedMemberFunctionImpl(
            { ownerBaseType.toBackendIr() },
            supertypeMemberFn.toBackendIr(),
            canonicalName
        )
    }
    override fun toBackendIr(): IrInheritedMemberFunction = backendIr

    override fun toString(): String {
        return "$canonicalName(${parameters.parameters.joinToString(separator = ", ", transform = { it.typeAtDeclarationTime.toString() })}) -> $returnType"
    }
}

private class IrFullyInheritedMemberFunctionImpl(
    private val getInheritingBaseType: () -> IrBaseType,
    override val superFunction: IrMemberFunction,
    override val canonicalName: CanonicalElementName.Function,
) : IrFullyInheritedMemberFunction, IrMemberFunction by superFunction {
    override val ownerBaseType: IrBaseType get() = getInheritingBaseType()
}