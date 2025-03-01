package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.reportings.Diagnosis
import compiler.reportings.Diagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundTopLevelFunction(
    context: MutableExecutionScopedCTContext,
    declaration: FunctionDeclaration,
    attributes: BoundFunctionAttributeList,
    declaredTypeParameters: List<BoundTypeParameter>,
    parameters: BoundParameterList,
    body: Body?,
) : BoundDeclaredFunction(
    context,
    declaration,
    attributes,
    declaredTypeParameters,
    parameters,
    body,
) {
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            context.sourceFile.packageName,
            name,
        )
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        super.semanticAnalysisPhase3(diagnosis)
        if (attributes.impliesNoBody) {
            if (body != null) {
                diagnosis.add(Diagnostic.illegalFunctionBody(declaration))
            }
        } else if (body == null) {
            diagnosis.add(Diagnostic.missingFunctionBody(declaration))
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