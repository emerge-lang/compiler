package compiler.binding.context

import compiler.binding.misc_ir.IrOverloadGroupImpl
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage

internal class IrPackageImpl(
    override val name: DotName,
    files: Iterable<SourceFile>,
) : IrPackage {
    override val functions: Set<IrOverloadGroup<IrFunction>> = files
        .flatMap { it.context.functions }
        .groupBy { it.name }
        .map { (functionName, overloads) ->
            IrOverloadGroupImpl(name + functionName, overloads)
        }
        .toSet()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as IrPackageImpl

        return name == other.name
    }

    override fun hashCode(): Int {
        return name.hashCode()
    }

    override fun toString() = name.toString()
}