package compiler.binding.expression

import compiler.CoreIntrinsicsModule
import compiler.InternalCompilerError
import compiler.StandardLibraryModule
import compiler.ast.expression.StringLiteralExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.binding.struct.Struct
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticByteArrayExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundStringLiteralExpression(
    override val context: CTContext,
    override val declaration: StringLiteralExpression,
) : BoundExpression<StringLiteralExpression> {
    override val isGuaranteedToThrow: Boolean = false
    override var type: BoundTypeReference? = null

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val defaultPackage = context.swCtx.getPackage(StandardLibraryModule.NAME)
            ?: throw InternalCompilerError("Standard Library module ${StandardLibraryModule.NAME} not present in software context")
        val stringType = defaultPackage.moduleContext.sourceFiles.asSequence()
            .map { it.context.resolveBaseType("String") }
            .filterNotNull()
            .firstOrNull()
            ?: throw InternalCompilerError("This software context doesn't define ${StandardLibraryModule.NAME}.String")

        type = stringType.baseReference.withMutability(TypeMutability.IMMUTABLE)
        return emptySet()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do
    }

    override fun toBackendIr(): IrExpression {
        val stringStruct = (type as RootResolvedTypeReference).baseType as Struct
        val staticDataType = stringStruct.resolveMemberVariable("utf8Data")!!.type!!
        val staticData = object : IrStaticByteArrayExpression {
            override val content = declaration.content.content.encodeToByteArray()
            override val evaluatesTo: IrType = staticDataType.toBackendIr()
        }
        val stringCtorInvocation = object : IrStaticDispatchFunctionInvocationExpression {
            override val function = stringStruct.constructors.single().toBackendIr()
            override val arguments = listOf(staticData)
            override val evaluatesTo = type!!.toBackendIr()
        }

        return stringCtorInvocation
    }
}