package compiler.reportings

import compiler.ast.AstFunctionAttribute
import compiler.ast.FunctionDeclaration

class SuperFunctionForOverrideNotFoundReporting(
    val overridingFunction: FunctionDeclaration,
) : Reporting(
    Level.ERROR,
    "Function ${overridingFunction.name.value} doesn't override anything. Check the name and the types.",
    overridingFunction.attributes.first { it is AstFunctionAttribute.Override }.sourceLocation,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is SuperFunctionForOverrideNotFoundReporting) return false

        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        return sourceLocation.hashCode()
    }
}