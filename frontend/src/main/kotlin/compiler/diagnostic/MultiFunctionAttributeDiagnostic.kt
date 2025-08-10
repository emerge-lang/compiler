package compiler.diagnostic

import compiler.ast.AstFunctionAttribute
import compiler.diagnostic.rendering.CellBuilder

abstract class MultiFunctionAttributeDiagnostic(
    severity: Severity,
    message: String,
    val attributes: Collection<AstFunctionAttribute>,
) : Diagnostic(severity, message, attributes.first().sourceLocation) {
    private val sourceLocations = attributes.map { it.sourceLocation }.toSet()

    init {
        require(sourceLocations.map { it.sourceFile }.toSet().size == 1)
    }

    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            sourceHints(sourceLocations.map { SourceHint(it, severity = severity) })
        }
    }

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