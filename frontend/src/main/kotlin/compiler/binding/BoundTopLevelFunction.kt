package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.IllegalMainSignatureDiagnostic
import compiler.diagnostic.illegalFunctionBody
import compiler.diagnostic.missingFunctionBody
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.github.tmarsteel.emerge.common.EmergeConstants

class BoundTopLevelFunction(
    parentContext: CTContext,
    annotations: BoundAnnotationSet,
    functionRootContext: MutableExecutionScopedCTContext,
    declaration: FunctionDeclaration,
    attributes: BoundFunctionAttributeList,
    declaredTypeParameters: List<BoundTypeParameter>,
    parameters: BoundParameterList,
    body: Body?,
) : BoundDeclaredFunction(
    parentContext,
    annotations,
    functionRootContext,
    declaration,
    attributes,
    declaredTypeParameters,
    parameters,
    body,
) {
    override val canonicalName by lazy {
        CanonicalElementName.Function(
            parentContext.packageName,
            name,
        )
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        super.semanticAnalysisPhase3(diagnosis)
        validateMainSignature(diagnosis)
        if (attributes.impliesNoBody) {
            if (body != null) {
                diagnosis.illegalFunctionBody(declaration)
            }
        } else if (body == null) {
            diagnosis.missingFunctionBody(declaration)
        }
    }

    /**
     * The entry point of a program takes no parameter, or the root token as its only one. The platform has nothing
     * else to pass.
     */
    private fun validateMainSignature(diagnosis: Diagnosis) {
        if (name != MAIN_FUNCTION_NAME) {
            return
        }

        val parameterTypes = parameters.parameters.map { it.typeAtDeclarationTime ?: return }
        val isLegal = when (parameterTypes.size) {
            0 -> true
            1 -> (parameterTypes.single() as? RootResolvedTypeReference)
                ?.takeUnless { it.isNullable }
                ?.baseType?.canonicalName == EmergeConstants.PlatformModule.WORLD_TYPE_NAME
            else -> false
        }
        if (!isLegal) {
            diagnosis.add(IllegalMainSignatureDiagnostic(parameters.parameters.first().declaration.span))
        }
    }

    companion object {
        const val MAIN_FUNCTION_NAME = "main"
    }

    private val backendIr by lazy { IrTopLevelFunctionImpl(this) }
    override fun toBackendIr(): IrFunction = backendIr
}

private class IrTopLevelFunctionImpl(
    private val boundFn: BoundTopLevelFunction,
) : IrFunction {
    override val canonicalName = boundFn.canonicalName
    override val parameters = boundFn.parameters.parameters.map { it.backendIrDeclaration }
    override val typeParameters by lazy { boundFn.declaredTypeParameters.map { it.toBackendIr() } }
    override val declaresReceiver = boundFn.declaresReceiver
    override val returnType by lazy { boundFn.returnType!!.toBackendIr() }
    override val isExternalC = boundFn.attributes.externalAttribute?.ffiName?.value == "C"
    override val externalSymbolName = boundFn.externalSymbolName
    override val isNothrow = boundFn.attributes.isDeclaredNothrow
    override val body: IrCodeChunk? by lazy { boundFn.getFullBodyBackendIr() }
    override val declaredAt = boundFn.declaredAt
}
