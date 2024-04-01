package compiler.binding.classdef

import compiler.binding.BoundDeclaredFunction
import compiler.reportings.Reporting

class BoundClassMemberFunction(
    val declaration: BoundDeclaredFunction,
) : BoundClassMember {
    override val name = declaration.name

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase3()
    }
}