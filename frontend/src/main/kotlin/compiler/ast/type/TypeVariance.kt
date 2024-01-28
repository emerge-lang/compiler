package compiler.ast.type

import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance

enum class TypeVariance(val backendIr: IrTypeVariance) {
    /** rename to invariant? */
    UNSPECIFIED(IrTypeVariance.INVARIANT),
    IN(IrTypeVariance.IN),
    OUT(IrTypeVariance.OUT),
    ;

    override fun toString() = when(this) {
        UNSPECIFIED -> "<${name.lowercase()}>"
        else -> name.lowercase()
    }
}