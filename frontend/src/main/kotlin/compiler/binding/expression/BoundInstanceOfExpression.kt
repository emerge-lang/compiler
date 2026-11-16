package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.expression.AstInstanceOfExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SoftwareContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.BoundFunction
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrReifiedTypeExpressionImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.ErroneousType
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeReflectionExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability

/**
 * Entirely syntax sugar; `v is T` desugars to a call to `emerge.core.reflection.isInstanceOf`, see [buildInstanceOf].
 */
class BoundInstanceOfExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstInstanceOfExpression,
    val expressionToCheck: BoundExpression<*>,
) : BoundExpression<AstInstanceOfExpression> {
    override val modifiedContext = expressionToCheck.modifiedContext

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        expressionToCheck.setNothrow(boundary)
    }

    override var type: BoundTypeReference? = null
        private set

    /**
     * is set during [semanticAnalysisPhase1]
     */
    var typeToCheck: BoundTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        expressionToCheck.semanticAnalysisPhase1(diagnosis)

        val fullTypeToCheck = context.resolveType(declaration.typeToCheck)
        fullTypeToCheck.validate(TypeUseSite.Irrelevant(declaration.operator.span, null), diagnosis)
        typeToCheck = validateTypeCheck(fullTypeToCheck)
        type = context.swCtx.bool.getBoundReferenceAssertNoTypeParameters(declaration.operator.span)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // nothing to do, always evaluates to bool
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        expressionToCheck.semanticAnalysisPhase2(diagnosis)
        expressionToCheck.setEvaluationResultUsage(
            TypeCheckValueUsage(context.swCtx, declaration.operator.span..declaration.typeToCheck.span),
        )
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // nothing to do:
        // the expression-to-be-checked is used regardless of context, with a type that doesn't depend on context (read Any)
        // the result of expression-to-be-checked is also never captured
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

/**
 * @return the type to check values against at runtime, for `is` and `as`; `null` if there is none to check against
 */
internal fun validateTypeCheck(fullTypeToCheck: BoundTypeReference): BoundTypeReference? {
    return fullTypeToCheck.takeUnless { it is ErroneousType }
}

/**
 * Whether checking against [this] takes no more than the base type of the object: a type without type arguments
 * that is not nullable. Then the check allocates nothing, see `emerge.core.reflection.isInstanceOf`.
 */
private val BoundTypeReference.isCheckedByBaseTypeAlone: Boolean
    get() = this is RootResolvedTypeReference && arguments.isNullOrEmpty()

/**
 * @return the overload of `emerge.core.reflection.isInstanceOf` whose second parameter is of the base type [typeParameterBaseType]
 */
private fun SoftwareContext.isInstanceOfFunction(typeParameterBaseType: BoundBaseType): BoundFunction {
    val reflectPackage = getPackage(reflectionBaseType.canonicalName.packageName)
        ?: throw InternalCompilerError("reflect package not found!")

    val isInstanceFn = reflectPackage.getTopLevelFunctionOverloadSetsBySimpleName("isInstanceOf")
        .asSequence()
        .filter { it.parameterCount == 2 }
        .flatMap { it.overloads }
        .filter { it.parameterTypes[0]!!.hasSameBaseTypeAs(any.getBoundReferenceAssertNoTypeParameters()) }
        .filter {
            val param2Type = it.parameterTypes[1]!!
            param2Type is RootResolvedTypeReference && param2Type.baseType == typeParameterBaseType
        }
        .singleOrNull()
        ?: throw InternalCompilerError("Could not unambiguously determine isInstanceOf(Any, ${typeParameterBaseType.simpleName}) function!")

    assert(isInstanceFn.returnType is RootResolvedTypeReference)
    assert((isInstanceFn.returnType as RootResolvedTypeReference).baseType == bool)
    return isInstanceFn
}

/**
 * @return an [IrExpression] that evaluates to `true` iff `value` is a value of the type [typeToCheck], type
 * arguments and nullability included, and `false` otherwise. Mutability is not checked, the runtime doesn't know it.
 */
internal fun buildInstanceOf(
    swCtx: SoftwareContext,
    value: IrTemporaryValueReference,
    typeToCheck: BoundTypeReference,
): IrImplicitEvaluationExpression {
    val isInstanceFn: BoundFunction
    val typeTemporary: IrCreateTemporaryValue
    val typeIsOwnedByThisCode: Boolean
    if (typeToCheck.isCheckedByBaseTypeAlone) {
        isInstanceFn = swCtx.isInstanceOfFunction(swCtx.reflectionBaseType)
        typeTemporary = IrCreateTemporaryValueImpl(
            IrBaseTypeReflectionExpressionImpl(
                (typeToCheck as RootResolvedTypeReference).baseType.toBackendIr(),
                IrSimpleTypeImpl(
                    swCtx.reflectionBaseType.toBackendIr(),
                    IrTypeMutability.IMMUTABLE,
                    isNullable = false,
                ),
            )
        )
        typeIsOwnedByThisCode = false
    } else {
        isInstanceFn = swCtx.isInstanceOfFunction(swCtx.reflectionType)
        typeTemporary = IrCreateTemporaryValueImpl(
            IrReifiedTypeExpressionImpl(
                typeToCheck.toBackendIr(),
                IrSimpleTypeImpl(
                    swCtx.reflectionType.toBackendIr(),
                    IrTypeMutability.IMMUTABLE,
                    isNullable = false,
                ),
            )
        )
        typeIsOwnedByThisCode = true
    }

    val isInstanceTemporary = IrCreateTemporaryValueImpl(
        IrStaticDispatchFunctionInvocationImpl(
            isInstanceFn.toBackendIr(),
            listOf(value, IrTemporaryValueReferenceImpl(typeTemporary)),
            emptyMap(),
            isInstanceFn.returnType!!.toBackendIr(),
            null, // isInstanceOf is declared nothrow
        )
    )

    return IrImplicitEvaluationExpressionImpl(
        IrCodeChunkImpl(listOfNotNull(
            typeTemporary,
            isInstanceTemporary,
            IrDropStrongReferenceStatementImpl(typeTemporary).takeIf { typeIsOwnedByThisCode },
        )),
        IrTemporaryValueReferenceImpl(isInstanceTemporary),
    )
}

internal class IrBaseTypeReflectionExpressionImpl(
    override val baseType: IrBaseType,
    override val evaluatesTo: IrType,
) : IrBaseTypeReflectionExpression
