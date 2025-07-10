package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.illegalFunctionBody
import compiler.diagnostic.missingFunctionBody
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundTopLevelFunction(
    parentContext: CTContext,
    functionRootContext: MutableExecutionScopedCTContext,
    declaration: FunctionDeclaration,
    attributes: BoundFunctionAttributeList,
    declaredTypeParameters: List<BoundTypeParameter>,
    parameters: BoundParameterList,
    body: Body?,
) : BoundDeclaredFunction(
    parentContext,
    functionRootContext,
    declaration,
    attributes,
    declaredTypeParameters,
    parameters,
    body,
) {
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            parentContext.sourceFile.packageName,
            name,
        )
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        super.semanticAnalysisPhase3(diagnosis)
        if (attributes.impliesNoBody) {
            if (body != null) {
                diagnosis.illegalFunctionBody(declaration)
            }
        } else if (body == null) {
            diagnosis.missingFunctionBody(declaration)
        }
    }

    private val backendIr by lazy { IrTopLevelFunctionImpl(this) }
    override fun toBackendIr(): IrFunction = backendIr
}

private class IrTopLevelFunctionImpl(
    private val boundFn: BoundTopLevelFunction,
) : IrFunction {
    override val canonicalName = boundFn.canonicalName
    override val parameters = boundFn.parameters.parameters.map { it.backendIrDeclaration }
    override val declaresReceiver = boundFn.declaresReceiver
    override val returnType by lazy { boundFn.returnType!!.toBackendIr() }
    override val isExternalC = boundFn.attributes.externalAttribute?.ffiName?.value == "C"
    override val isNothrow = boundFn.attributes.isDeclaredNothrow
    override val body: IrCodeChunk? by lazy { boundFn.getFullBodyBackendIr() }
    override val declaredAt = boundFn.declaredAt
}