package compiler.binding

import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrDeclaredFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrImplementedFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

internal abstract class IrFunctionImpl private constructor(
    val canonicalName: CanonicalElementName.Function,
    private val boundFunction: BoundFunction,
    boundBody: BoundFunction.Body?,
) {
    protected val _parameters: List<IrVariableDeclaration> by lazy { boundFunction.parameters.parameters.map { it.backendIrDeclaration } }
    protected val _returnType = boundFunction.returnType!!.toBackendIr()
    protected val _isExternalC = boundFunction.attributes.externalAttribute?.ffiName?.value == "C"

    protected val _body: IrCodeChunk by lazy {
        when (boundBody) {
            null -> IrCodeChunkImpl(emptyList())
            is BoundFunction.Body.Full -> boundBody.code.toBackendIrStatement() // TODO: implicit unit return
            is BoundFunction.Body.SingleExpression -> {
                val resultTemporary = IrCreateTemporaryValueImpl(boundBody.expression.toBackendIrExpression())
                IrCodeChunkImpl(listOf(
                    resultTemporary,
                    object : IrReturnStatement {
                        override val value = IrTemporaryValueReferenceImpl(resultTemporary)
                    },
                ))
            }
        }
    }

    private class IrDeclaredFunctionImpl(
        canonicalName: CanonicalElementName.Function,
        boundFunction: BoundFunction,
    ) : IrFunctionImpl(canonicalName, boundFunction, null), IrDeclaredFunction {
        override val parameters = super._parameters
        override val returnType = super._returnType
        override val isExternalC = super._isExternalC
    }

    private class IrImplementedFunctionImpl(
        canonicalName: CanonicalElementName.Function,
        boundFunction: BoundFunction,
        code: BoundFunction.Body,
    ) : IrFunctionImpl(canonicalName, boundFunction, code), IrImplementedFunction {
        override val parameters = super._parameters
        override val returnType = super._returnType
        override val isExternalC = super._isExternalC

        override val body = super._body
    }

    override fun toString(): String {
        return "IrFunction[$canonicalName] declared in ${boundFunction.declaredAt.fileLineColumnText}"
    }

    companion object {
        operator fun invoke(function: BoundFunction): IrFunction {
            return when {
                function is BoundDeclaredFunction && function.code != null -> {
                    IrImplementedFunctionImpl(function.canonicalName, function, function.code)
                }
                else -> {
                    IrDeclaredFunctionImpl(function.canonicalName, function)
                }
            }
        }
    }
}