package compiler.binding.context

import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext

internal class IrSoftwareContextImpl(
    private val _modules: Iterable<ModuleContext>
) : IrSoftwareContext {
    override val modules: Set<IrModule> = _modules.map { it.toBackendIr() }.toSet()
}