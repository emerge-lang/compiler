package compiler.binding

import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.common.CanonicalElementName

internal abstract class IrFunctionImpl private constructor(
    val canonicalName: CanonicalElementName.Function,
    private val boundFunction: BoundDeclaredFunction,
    boundBody: BoundDeclaredFunction.Body?,
) {
    protected val _parameters: List<IrVariableDeclaration> by lazy { boundFunction.parameters.parameters.map { it.backendIrDeclaration } }
    protected val _returnType = boundFunction.returnType!!.toBackendIr()
    protected val _isExternalC = boundFunction.attributes.externalAttribute?.ffiName?.value == "C"



    override fun toString(): String {
        return "IrFunction[$canonicalName] declared in ${boundFunction.declaredAt.fileLineColumnText}"
    }
}