package compiler.reportings

import compiler.binding.type.BaseType
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.SourceLocation

class TypeArgumentCountMismatchReporting(
    val erroneousRef: RootResolvedTypeReference,
    val baseType: BaseType,
) : Reporting(
    Level.ERROR,
    "Type ${baseType.simpleName} requires ${baseType.parameters.size} type parameters, got ${erroneousRef.arguments.size}",
    erroneousRef.original?.declaringNameToken?.sourceLocation ?: SourceLocation.UNKNOWN,
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeArgumentCountMismatchReporting

        if (erroneousRef != other.erroneousRef) return false
        if (sourceLocation != other.sourceLocation) return false

        return true
    }

    override fun hashCode(): Int {
        var result = erroneousRef.hashCode()
        result = 31 * result + sourceLocation.hashCode()
        return result
    }
}