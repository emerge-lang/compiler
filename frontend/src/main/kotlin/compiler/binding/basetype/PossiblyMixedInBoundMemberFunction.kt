package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.binding.BoundMemberFunction
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.IrClassFieldAccessExpressionImpl
import compiler.binding.expression.IrDynamicDispatchFunctionInvocationImpl
import compiler.binding.expression.IrReturnStatementImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDelegatingMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrInheritedMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

/**
 * This is used in [BoundBaseType.Kind.CLASS]es only, for [InheritedBoundMemberFunction]s where no matching
 * override is found. Once the classes constructor is analyzed, a mixin can be assigned to this function. If
 * no mixin is assigned, this will report an [AbstractInheritedFunctionNotImplementedReporting] in [semanticAnalysisPhase3].
 */
class PossiblyMixedInBoundMemberFunction(
    override val ownerBaseType: BoundBaseType,
    val inheritedFn: InheritedBoundMemberFunction,
) : BoundMemberFunction by inheritedFn {
    private var mixinRegistration: ExecutionScopedCTContext.MixinRegistration? = null
    fun assignMixin(mixinRegistration: ExecutionScopedCTContext.MixinRegistration) {
        if (this.mixinRegistration != null) {
            throw InternalCompilerError("Assigning two mixins to a single delegating function")
        }
        this.mixinRegistration = mixinRegistration
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return inheritedFn.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return inheritedFn.semanticAnalysisPhase2()
    }

    override val overrides: Set<InheritedBoundMemberFunction> = setOf(inheritedFn)

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = inheritedFn.semanticAnalysisPhase3().toMutableSet()
        if (mixinRegistration == null) {
            reportings.add(Reporting.abstractInheritedFunctionNotImplemented(ownerBaseType, inheritedFn.supertypeMemberFn))
        }
        return reportings
    }

    private val backendIr by lazy {
        val inheritedFnIr = inheritedFn.toBackendIr()
        val parametersIr = inheritedFnIr.parameters.map(::IrDelegatedMethodParameter)
        val field = mixinRegistration!!.obtainField()
        val fieldIr = field.toBackendIr()

        val mixinHostTypeIr = inheritedFn.ownerBaseType.baseReference.toBackendIr()
        val selfTemporary = IrCreateTemporaryValueImpl(
            IrVariableAccessExpressionImpl(parametersIr.first()),
            mixinHostTypeIr,
        )
        val fieldValueTemporary = IrCreateTemporaryValueImpl(
            IrClassFieldAccessExpressionImpl(
                IrTemporaryValueReferenceImpl(selfTemporary),
                fieldIr,
                fieldIr.type,
            )
        )

        val parameterTemporaries = parametersIr.drop(1).map { paramIr ->
            IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(paramIr))
        }
        val invocationExpr = IrCreateTemporaryValueImpl(IrDynamicDispatchFunctionInvocationImpl(
            IrTemporaryValueReferenceImpl(fieldValueTemporary),
            inheritedFn.supertypeMemberFn.toBackendIr(),
            listOf(IrTemporaryValueReferenceImpl(fieldValueTemporary)) + parameterTemporaries.map(::IrTemporaryValueReferenceImpl),
            emptyMap(),
            inheritedFnIr.returnType,
            null,
        ))
        val returnStmt = IrReturnStatementImpl(IrTemporaryValueReferenceImpl(invocationExpr))

        IrDelegatingMemberFunctionImpl(
            inheritedFn.toBackendIr(),
            parametersIr,
            fieldIr,
            IrCodeChunkImpl(listOf(
                selfTemporary,
                fieldValueTemporary
            ) + parameterTemporaries + listOf(
                invocationExpr,
                returnStmt,
            )),
        )
    }

    override fun toBackendIr(): IrMemberFunction {
        return backendIr
    }

    override fun toString() = "$inheritedFn by mixin $mixinRegistration"
}

private class IrDelegatingMemberFunctionImpl(
    val inheritedFn: IrInheritedMemberFunction,
    override val parameters: List<IrVariableDeclaration>,
    override val delegatesTo: IrClass.Field,
    override val body: IrCodeChunk,
) : IrDelegatingMemberFunction, IrMemberFunction by inheritedFn {
    override val superFunction = inheritedFn.superFunction
    override val supportsDynamicDispatch = true
    override val overrides = setOf(inheritedFn)
}

private class IrDelegatedMethodParameter(
    private val parameterInInheritedFn: IrVariableDeclaration
) : IrVariableDeclaration by parameterInInheritedFn