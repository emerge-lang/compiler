package compiler.binding.expression

import compiler.ast.expression.AstReflectExpression
import compiler.ast.type.TypeMutability
import compiler.binding.ImpurityVisitor
import compiler.binding.SideEffectPrediction
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.unsupportedReflection
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeReflectionExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundReflectExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstReflectExpression
) : BoundExpression<AstReflectExpression> {
    override val throwBehavior = SideEffectPrediction.NEVER
    override val returnBehavior = SideEffectPrediction.NEVER

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        // nothing to do
    }

    private lateinit var typeToReflectOn: BoundTypeReference

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        typeToReflectOn = context.resolveType(declaration.type)
        typeToReflectOn.validate(
            TypeUseSite.Irrelevant(declaration.span, null),
            diagnosis,
        )
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {

    }

    override fun setUsageContext(usedAsType: BoundTypeReference, captured: Boolean) {
        // nothing to do, this expression doesn't use any values
    }

    private var baseTypeToReflectOn: BoundBaseType? = null

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        if (typeToReflectOn is RootResolvedTypeReference) {
            baseTypeToReflectOn = (typeToReflectOn as RootResolvedTypeReference).baseType
        } else if (typeToReflectOn !is UnresolvedType) {
            diagnosis.unsupportedReflection(typeToReflectOn)
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    override val type: BoundTypeReference
        get() = context.swCtx.reflectionBaseType.baseReference.withMutability(TypeMutability.IMMUTABLE)

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {

    }

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = true

    override fun toBackendIrExpression(): IrExpression {
        return IrBaseTypeReflectionExpressionImpl(
            this.baseTypeToReflectOn!!.toBackendIr(),
            this.type.toBackendIr(),
        )
    }
}

internal class IrBaseTypeReflectionExpressionImpl(
    override val baseType: IrBaseType,
    override val evaluatesTo: IrType,
) : IrBaseTypeReflectionExpression