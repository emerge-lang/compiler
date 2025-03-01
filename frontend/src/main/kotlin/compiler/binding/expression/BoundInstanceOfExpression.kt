package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.expression.AstInstanceOfExpression
import compiler.ast.type.TypeMutability
import compiler.binding.ImpurityVisitor
import compiler.binding.IrCodeChunkImpl
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SoftwareContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.reportings.Diagnosis
import compiler.reportings.Diagnostic
import compiler.reportings.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference

/**
 * Entirely syntax sugar; `v is T` desugars to `isInstance(v, reflect T)`,
 * plus an import of `emerge.core.reflection.isInstance`.
 */
class BoundInstanceOfExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstInstanceOfExpression,
    val expressionToCheck: BoundExpression<*>,
) : BoundExpression<AstInstanceOfExpression> {
    override val throwBehavior get() = expressionToCheck.throwBehavior
    override val returnBehavior get() = expressionToCheck.returnBehavior

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        expressionToCheck.setNothrow(boundary)
    }

    override var type: BoundTypeReference? = null
        private set

    /**
     * is set during [semanticAnalysisPhase1]
     */
    var typeToCheck: BoundBaseType? = null
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        expressionToCheck.semanticAnalysisPhase1(diagnosis)

        val fullTypeToCheck = context.resolveType(declaration.typeToCheck)
        fullTypeToCheck.validate(TypeUseSite.Irrelevant(declaration.operator.span, null), diagnosis)
        typeToCheck = validateTypeCheck(this, fullTypeToCheck, diagnosis)
        type = context.swCtx.bool.baseReference
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // nothing to do, always evaluates to bool
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expressionToCheck.semanticAnalysisPhase2(diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        expressionToCheck.semanticAnalysisPhase3(diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expressionToCheck.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expressionToCheck.visitWritesBeyond(boundary, visitor)
    }

    override val isEvaluationResultReferenceCounted = true
    override val isEvaluationResultAnchored = false
    override val isCompileTimeConstant = expressionToCheck.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        return buildNothrowInvocationLikeIr(
            listOf(this.expressionToCheck),
            buildActualCall = { args -> buildInstanceOf(context.swCtx, args.single(), this.typeToCheck!!) },
        )
    }
}

internal fun validateTypeCheck(node: BoundExpression<*>, fullTypeToCheck: BoundTypeReference, diagnosis: Diagnosis): BoundBaseType? {
    if (fullTypeToCheck is RootResolvedTypeReference) {
        return fullTypeToCheck.baseType
        // TODO: warn about unchecked type arguments!!
    }

    if (fullTypeToCheck !is UnresolvedType) {
        diagnosis.add(Diagnostic.typeCheckOnVolatileTypeParameter(node, fullTypeToCheck))
    }

    return null
}

/**
 * @return an [IrExpression] that evaluates to `true` iff `value` refers to an object of type [typeToCheck],
 * and `false` otherwise.
 */
internal fun buildInstanceOf(
    swCtx: SoftwareContext,
    value: IrTemporaryValueReference,
    typeToCheck: BoundBaseType
): IrImplicitEvaluationExpression {
    val reflectPackage = swCtx.getPackage(swCtx.reflectionBaseType.canonicalName.packageName)
        ?: throw InternalCompilerError("reflect package not found!")

    val isInstanceFn = reflectPackage.getTopLevelFunctionOverloadSetsBySimpleName("isInstanceOf")
        .asSequence()
        .filter { it.parameterCount == 2 }
        .flatMap { it.overloads }
        .filter { it.parameterTypes[0]!!.hasSameBaseTypeAs(swCtx.any.baseReference) }
        .filter {
            val param2Type = it.parameterTypes[1]!!
            param2Type is RootResolvedTypeReference && param2Type.baseType == swCtx.reflectionBaseType
        }
        .singleOrNull()
        ?: throw InternalCompilerError("Could not unambiguously determine isInstanceOf(Any, ReflectionBaseType) function!")

    assert(isInstanceFn.returnType is RootResolvedTypeReference)
    assert((isInstanceFn.returnType as RootResolvedTypeReference).baseType == swCtx.bool)

    val reflectionObjectTemporary = IrCreateTemporaryValueImpl(
        IrBaseTypeReflectionExpressionImpl(
            typeToCheck.toBackendIr(),
            swCtx.reflectionBaseType.baseReference.withMutability(TypeMutability.IMMUTABLE).toBackendIr(),
        )
    )

    val isInstanceTemporary = IrCreateTemporaryValueImpl(
        IrStaticDispatchFunctionInvocationImpl(
            isInstanceFn.toBackendIr(),
            listOf(value, IrTemporaryValueReferenceImpl(reflectionObjectTemporary)),
            emptyMap(),
            isInstanceFn.returnType!!.toBackendIr(),
            null, // isInstanceOf is declared nothrow
        )
    )

    return IrImplicitEvaluationExpressionImpl(
        IrCodeChunkImpl(listOf(
            reflectionObjectTemporary,
            isInstanceTemporary
        )),
        IrTemporaryValueReferenceImpl(isInstanceTemporary),
    )
}