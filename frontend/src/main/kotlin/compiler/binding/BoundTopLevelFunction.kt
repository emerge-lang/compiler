package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeParameter
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction

class BoundTopLevelFunction(
    context: CTContext,
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
    override val isVirtual = false
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            context.sourceFile.packageName,
            name,
        )
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = super.semanticAnalysisPhase3().toMutableList()
        if (attributes.impliesNoBody) {
            if (body != null) {
                reportings.add(Reporting.illegalFunctionBody(declaration))
            }
        } else if (body == null) {
            reportings.add(Reporting.missingFunctionBody(declaration))
        }

        return reportings
    }

    private val backendIr by lazy { IrTopLevelFunctionImpl(this) }
    override fun toBackendIr(): IrFunction = backendIr
}

private class IrTopLevelFunctionImpl(
    private val boundFn: BoundTopLevelFunction,
) : IrFunction {
    override val canonicalName = boundFn.canonicalName
    override val parameters = boundFn.parameters.parameters.map { it.backendIrDeclaration }
    override val returnType by lazy { boundFn.returnType!!.toBackendIr() }
    override val isExternalC = boundFn.attributes.externalAttribute?.ffiName?.value == "C"
    override val body: IrCodeChunk? by lazy { boundFn.body?.toBackendIr() }
}