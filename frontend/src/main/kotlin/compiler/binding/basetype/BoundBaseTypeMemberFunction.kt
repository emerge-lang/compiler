package compiler.binding.basetype

import compiler.ast.ClassEntryDeclaration
import compiler.binding.BoundDeclaredFunction
import compiler.binding.DefinitionWithVisibility
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

class BoundBaseTypeMemberFunction(
    override val context: CTContext,
    override val declaration: ClassEntryDeclaration,
    val functionInstance: BoundDeclaredFunction,
) : BoundBaseTypeEntry<ClassEntryDeclaration>, DefinitionWithVisibility {
    val name = functionInstance.name
    override val visibility get()= functionInstance.attributes.visibility

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return functionInstance.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return functionInstance.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return functionInstance.semanticAnalysisPhase3()
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return functionInstance.visibility.validateAccessFrom(location, this)
    }

    override fun toStringForErrorMessage() = "member function $name"
}