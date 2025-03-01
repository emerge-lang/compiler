package compiler.diagnostic

import compiler.ast.AstFunctionAttribute

abstract class MultiFunctionAttributeDiagnostic(
    level: Level,
    message: String,
    val attributes: Collection<AstFunctionAttribute>,
) : Diagnostic(level, message, attributes.first().sourceLocation) {
    private val sourceLocations = attributes.map { it.sourceLocation }.toSet()

    init {
        require(sourceLocations.map { it.sourceFile }.toSet().size == 1)
    }

    override fun toString() = "$levelAndMessage\nin ${illustrateSourceLocations(sourceLocations)}"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other == null || this.javaClass != other.javaClass) return false
        other as MultiFunctionAttributeDiagnostic

        if (this.sourceLocations != other.sourceLocations) return false

        return true
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + sourceLocations.hashCode()

        return result
    }
}