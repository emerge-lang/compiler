package compiler.binding

import compiler.binding.expression.BoundExpression
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrFunctionParameter
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement

internal abstract class IrFunctionImpl private constructor(
    override val fqn: DotName,
    private val boundFunction: BoundFunction,
    boundBody: BoundExecutable<*>?,
) : IrImplementedFunction {
    override val parameters: List<IrFunctionParameter> = boundFunction.parameters.parameters.map { Parameter(it) }
    override val returnType = boundFunction.returnType!!.toBackendIr()

    override val body: IrCodeChunk = when (boundBody) {
        null -> IrCodeChunkImpl(emptyList())
        is BoundCodeChunk -> boundBody.toBackendIr()
        is BoundExpression<*> -> IrCodeChunkImpl(listOf(object : IrReturnStatement {
            override val value = boundBody.toBackendIr()
        }))
        else -> IrCodeChunkImpl(listOf(
            boundBody.toBackendIr(),
            // TODO: implicit unit return
        ))
    }

    private class Parameter(private val param: BoundParameter) : IrFunctionParameter {
        override val name = param.name
        override val type = param.type!!.toBackendIr()
    }

    private class IrDeclaredFunctionImpl(
        fqn: DotName,
        boundFunction: BoundFunction,
    ) : IrFunctionImpl(fqn, boundFunction, null)

    private class IrImplementedFunctionImpl(
        fqn: DotName,
        boundFunction: BoundDeclaredFunction,
    ) : IrFunctionImpl(fqn, boundFunction, boundFunction.code!!)

    override fun toString(): String {
        return "IrFunction[$fqn] declared in ${boundFunction.declaredAt.fileLineColumnText}"
    }

    companion object {
        operator fun invoke(function: BoundFunction): IrFunction {
            return if (function is BoundDeclaredFunction && function.code != null) {
                IrImplementedFunctionImpl(function.fullyQualifiedName, function)
            } else {
                IrDeclaredFunctionImpl(function.fullyQualifiedName, function)
            }
        }
    }
}