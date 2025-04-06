package compiler.binding.expression

import compiler.ast.VariableOwnership
import compiler.ast.expression.ArrayLiteralExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction.Companion.reduceSequentialExecution
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullInitializedArrayExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.common.indexed
import java.math.BigInteger

class BoundArrayLiteralExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: ArrayLiteralExpression,
    val elements: List<BoundExpression<*>>,
) : BoundLiteralExpression<ArrayLiteralExpression> {
    override val modifiedContext: ExecutionScopedCTContext = elements.lastOrNull()?.modifiedContext ?: context

    override val throwBehavior get() = elements.map { it.throwBehavior }.reduceSequentialExecution()
    override val returnBehavior get() = elements.map { it.returnBehavior }.reduceSequentialExecution()

    private var expectedEvaluationResultType: BoundTypeReference? = null
    private var expectedElementType: BoundTypeReference? = null
    override var type: BoundTypeReference? = null
        private set

    override val isEvaluationResultAnchored = false

    private val arrayType: BoundBaseType by lazy {
        context.swCtx.array
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return elements.forEach { it.semanticAnalysisPhase1(diagnosis) }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        elements.forEach { it.markEvaluationResultUsed() }
        elements.forEach { it.semanticAnalysisPhase2(diagnosis) }

        val elementType: BoundTypeReference
        if (expectedElementType != null) {
            elementType = expectedElementType!!
            elements.forEach { element ->
                element.type?.let {
                    val unification = elementType.unify(it, element.declaration.span, TypeUnification.EMPTY)
                    unification.diagnostics.forEach(diagnosis::add)
                }
            }
        } else {
            elementType = elements
                .mapNotNull { it.type }
                .reduceOrNull(BoundTypeReference::closestCommonSupertypeWith)
                ?: context.swCtx.any.baseReference
        }

        type = RootResolvedTypeReference(
            TypeReference(arrayType.simpleName),
            arrayType,
            listOf(BoundTypeArgument(
                context,
                TypeArgument(TypeVariance.UNSPECIFIED, TypeReference("_")),
                TypeVariance.UNSPECIFIED,
                elementType,
            ))
        )
        expectedEvaluationResultType?.let {
            type = type?.withMutability(it.mutability)
        }

        val valueUsage = CreateReferenceValueUsage(elementType, declaration.leftBracket.span .. declaration.rightBracket.span, VariableOwnership.CAPTURED)
        elements.forEach {
            it.setEvaluationResultUsage(valueUsage)
        }
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        elements.forEach { it.setNothrow(boundary) }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return elements.forEach { it.semanticAnalysisPhase3(diagnosis) }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        elements.forEach {
            it.visitReadsBeyond(boundary, visitor)
        }
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        elements.forEach {
            it.visitWritesBeyond(boundary, visitor)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        elements.forEach { it.setExpectedReturnType(type, diagnosis) }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expectedEvaluationResultType = type

        if (type !is RootResolvedTypeReference || type.baseType != arrayType) {
            // ignore
            return
        }

        expectedElementType = type.arguments?.firstOrNull()?.type ?: return
        elements.forEach { it.setExpectedEvaluationResultType(expectedElementType!!, diagnosis) }
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // not relevant
    }

    override val isEvaluationResultReferenceCounted = true

    override val isCompileTimeConstant: Boolean
        get() = elements.all { it.isCompileTimeConstant }

    override fun toBackendIrExpression(): IrExpression {
        val arraySetFn = context.swCtx.array.resolveMemberFunction("setOrPanic")
            .single()
            .overloads
            .single()
            .also {
                check(it.parameters.parameters.size == 3)
                check((it.returnType as RootResolvedTypeReference).baseType == context.swCtx.unit)
            }
            .toBackendIr()

        val irType = type!!.toBackendIr()
        val irElementType = (type as RootResolvedTypeReference).arguments!!.single().type.toBackendIr()

        return buildGenericInvocationLikeIr(
            context,
            declaration.span,
            elements,
            { args, landingpad ->
                val arrayTemporary = IrCreateTemporaryValueImpl(
                    IrNullInitializedArrayExpressionImpl(irType, irElementType, args.size.toULong(), landingpad!!)
                )
                val arrayTemporaryRef = IrTemporaryValueReferenceImpl(arrayTemporary)
                val instrs = mutableListOf<IrExecutable>()
                instrs.add(arrayTemporary)
                for ((index, element) in args.indexed()) {
                    val indexTemporary = IrCreateTemporaryValueImpl(
                        IrIntegerLiteralExpressionImpl(
                            BigInteger.valueOf(index.toLong()),
                            IrSimpleTypeImpl(context.swCtx.uword.toBackendIr(), IrTypeMutability.IMMUTABLE, false)
                        )
                    )
                    instrs.add(indexTemporary)
                    instrs.add(IrCreateTemporaryValueImpl(
                        IrStaticDispatchFunctionInvocationImpl(
                            arraySetFn,
                            listOf(
                                arrayTemporaryRef,
                                IrTemporaryValueReferenceImpl(indexTemporary),
                                element,
                            ),
                            mapOf(
                                (type as RootResolvedTypeReference).baseType.typeParameters!!.single().name to irElementType,
                            ),
                            IrSimpleTypeImpl(context.swCtx.unit.toBackendIr(), IrTypeMutability.IMMUTABLE,false),
                            null, // the set will not throw, index is guaranteed to be in bounds
                        ),
                    ))
                }
                IrImplicitEvaluationExpressionImpl(IrCodeChunkImpl(instrs), arrayTemporaryRef)
            },
            assumeNothrow = false, // array ctor can always throw an OOM error
        )
    }
}

private class IrNullInitializedArrayExpressionImpl(
    override val evaluatesTo: IrType,
    override val elementType: IrType,
    override val size: ULong,
    override val oomLandingpad: IrInvocationExpression.Landingpad,
) : IrNullInitializedArrayExpression