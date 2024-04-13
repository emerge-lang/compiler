package compiler.binding.context

import io.github.tmarsteel.emerge.backend.api.PackageName
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage

internal class IrModuleImpl(
    private val _context: ModuleContext
) : IrModule {
    override val name: PackageName = _context.moduleName
    override val packages: Set<IrPackage> = _context.nonEmptyPackages
        .map { packageContext ->
            IrPackageImpl(packageContext)
        }
        .toSet()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as IrModuleImpl

        return name == other.name
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }

    override fun toString(): String {
        return _context.moduleName.toString()
    }
}