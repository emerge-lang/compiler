package compiler.binding.basetype

import compiler.binding.BoundDeclaredFunction
import compiler.binding.DefinitionWithVisibility
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

class BoundBaseTypeMemberFunction(
    val declaration: BoundDeclaredFunction,
) : BoundBaseTypeEntry, DefinitionWithVisibility {
    val name = declaration.name
    override val visibility get()= declaration.attributes.visibility

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return declaration.semanticAnalysisPhase3()
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return declaration.visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "member function $name"
}