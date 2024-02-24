package compiler.binding.context

import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrOverloadGroupImpl
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrGlobalVariable
import io.github.tmarsteel.emerge.backend.api.ir.IrOverloadGroup
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

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

    override val structs: Set<IrStruct> = files
        .flatMap { it.context.structs }
        .map { it.toBackendIr() }
        .toSet()

    override val variables: Set<IrGlobalVariable> = files
        .flatMap { it.context.variables }
        .map {
            val initializer = it.initializerExpression
                ?: throw CodeGenerationException("Missing initializer for global variable ${this.name.plus(it.name)}")

            IrGlobalVariableImpl(
                it.backendIrDeclaration,
                initializer,
            )
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

internal class IrGlobalVariableImpl(
    override val declaration: IrVariableDeclaration,
    private val boundInitialValue: BoundExpression<*>,
) : IrGlobalVariable {
    override val initializer get() = boundInitialValue.toBackendIrExpression()
}