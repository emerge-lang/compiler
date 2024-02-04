package compiler.binding

import compiler.binding.expression.BoundExpression
import io.github.tmarsteel.emerge.backend.api.DotName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDeclaredFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

internal abstract class IrFunctionImpl private constructor(
    val fqn: DotName,
    private val boundFunction: BoundFunction,
    boundBody: BoundExecutable<*>?,
) {
    protected val _parameters: List<IrVariableDeclaration> = boundFunction.parameters.parameters.map { it.backendIrDeclaration }
    protected val _returnType = boundFunction.returnType!!.toBackendIr()

    protected val _body: IrCodeChunk = when (boundBody) {
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

    private class IrDeclaredFunctionImpl(
        fqn: DotName,
        boundFunction: BoundFunction,
    ) : IrFunctionImpl(fqn, boundFunction, null), IrDeclaredFunction {
        override val parameters = super._parameters
        override val returnType = super._returnType
    }

    private class IrImplementedFunctionImpl(
        fqn: DotName,
        boundFunction: BoundDeclaredFunction,
    ) : IrFunctionImpl(fqn, boundFunction, boundFunction.code!!), IrImplementedFunction {
        override val parameters = super._parameters
        override val returnType = super._returnType
        override val body = super._body
    }

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