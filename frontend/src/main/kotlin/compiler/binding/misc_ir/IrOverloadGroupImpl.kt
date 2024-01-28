package compiler.binding.misc_ir

import compiler.binding.BoundFunction
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup

internal class IrOverloadGroupImpl(
    override val fqn: DotName,
    overloads: Iterable<BoundFunction>
) : IrOverloadGroup<IrFunction> {
    override val overloads: Set<IrFunction> by lazy { overloads.map { it.toBackendIr() }.toSet() }

    override fun toString(): String = "OverloadGroup[$fqn, n = ${overloads.size}]"
}