package compiler.binding.misc_ir

import compiler.binding.BoundFunction
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup

internal class IrOverloadGroupImpl(
    override val canonicalName: CanonicalElementName.Function,
    override val parameterCount: Int,
    overloads: Iterable<BoundFunction>
) : IrOverloadGroup<IrFunction> {
    override val overloads: Set<IrFunction> by lazy { overloads.map { it.toBackendIr() }.toSet() }

    override fun toString(): String = "OverloadGroup[$canonicalName, n params = $parameterCount, n impls = ${overloads.size}]"

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IrOverloadGroupImpl) return false

        if (canonicalName != other.canonicalName) return false
        if (parameterCount != other.parameterCount) return false

        return true
    }

    override fun hashCode(): Int {
        var result = canonicalName.hashCode()
        result = 31 * result + parameterCount
        return result
    }
}