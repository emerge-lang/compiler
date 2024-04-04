package compiler.reportings

import compiler.InternalCompilerError
import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.BoundVisibility
import compiler.binding.classdef.BoundClassDefinition
import compiler.binding.classdef.BoundClassMemberFunction
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.lexer.SourceLocation

class ElementNotAccessibleReporting(
    val element: Any,
    val visibility: BoundVisibility,
    val accessAt: SourceLocation
) : Reporting(
    Level.ERROR,
    run {
        val elementDescription = when(element) {
            is BoundClassDefinition -> "class ${element.simpleName}"
            is BoundClassMemberFunction -> "member function ${element.name}"
            is BoundClassMemberVariable -> "member variable ${element.name}"
            is BoundFunction -> "function ${element.name}"
            is BoundVariable -> "variable ${element.name}"
            else -> throw InternalCompilerError("unsupported element type ${element::class.qualifiedName}")
        }

        val visibilityDescription = when(visibility) {
            is BoundVisibility.ExportedScope -> throw InternalCompilerError("exported elements are always accessible... ?")
            is BoundVisibility.FileScope -> "private in file ${visibility.lexerFile}"
            is BoundVisibility.ModuleScope -> "internal to module ${visibility.moduleName}"
            is BoundVisibility.PackageScope -> "internal to package ${visibility.packageName}"
        }

        "$elementDescription is $visibilityDescription, cannot be accessed here"
    },
    accessAt,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ElementNotAccessibleReporting) return false

        if (element !== other.element) return false
        if (accessAt != other.accessAt) return false

        return true
    }

    override fun hashCode(): Int {
        var result = System.identityHashCode(element)
        result = 31 * result + accessAt.hashCode()
        return result
    }
}