package compiler.binding.basetype

import compiler.binding.BoundMemberFunction
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDelegatingMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction

class DelegatedBoundMemberFunction(
    val inheritedFn: InheritedBoundMemberFunction,
    val delegatedTo: BaseTypeField,
    val delegationDeclaredAt: Span,
) : BoundMemberFunction by inheritedFn {
    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return inheritedFn.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return inheritedFn.semanticAnalysisPhase2()
    }

    override val overrides: Set<InheritedBoundMemberFunction> = setOf(inheritedFn)

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return inheritedFn.semanticAnalysisPhase3()
    }

    private val backendIr by lazy {
        IrDelegatingMemberFunctionImpl(
            inheritedFn.supertypeMemberFn.toBackendIr(),
            delegatedTo.toBackendIr(),
            TODO(),
        )
    }

    override fun toBackendIr(): IrMemberFunction {
        return backendIr
    }

    override fun toString() = "$inheritedFn by mixin in $delegatedTo"
}

private class IrDelegatingMemberFunctionImpl(
    override val superFunction: IrMemberFunction,
    override val delegatesTo: IrClass.Field,
    override val body: IrCodeChunk,
) : IrDelegatingMemberFunction, IrMemberFunction by superFunction {
}