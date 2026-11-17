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
import compiler.ast.type.TypeMutability
import compiler.binding.BoundVariable
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression.ImplyingResult
import compiler.binding.type.ErroneousType
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.TypeCheckKind
import compiler.diagnostic.typeCheckAlwaysSucceeds
import compiler.diagnostic.typeCheckNeverSucceeds
import compiler.binding.type.StaticTypeCheckResult
import compiler.lexer.Span
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

        staticResult = reportStaticResultOfTypeCheck(
            TypeCheckKind.INSTANCE_OF,
            expressionToCheck.type,
            typeToCheck,
            declaration.operator.span..declaration.typeToCheck.span,
            diagnosis,
        )
    }

    /** is set during [semanticAnalysisPhase2] */
    private var staticResult: StaticTypeCheckResult = StaticTypeCheckResult.Unknown

    override val implications: List<BoundExpression.ResultImplication> get() {
        val localTypeToCheck = typeToCheck
        val subject = (expressionToCheck as? BoundIdentifierExpression)
            ?.let { it.referral as? BoundIdentifierExpression.ReferringVariable }
            ?.variable

        if (localTypeToCheck == null || localTypeToCheck is ErroneousType || subject == null) {
            return emptyList()
        }

        return listOf(BoundExpression.ResultImplication(
            ImplyingResult.BOOL_TRUE,
            mapOf(subject to BoundVariable.TypeRefinement(intersectWith = localTypeToCheck))
        ))
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
            buildActualCall = { args ->
                if (staticResult == StaticTypeCheckResult.AlwaysSucceeds) {
                    // the value is evaluated still, for its side effects
                    IrBooleanLiteralExpressionImpl(type!!.toBackendIr(), true)
                } else {
                    buildInstanceOf(context.swCtx, args.single(), this.typeToCheck!!, expressionToCheck.type)
                }
            },
        )
    }
}

/**
 * Reports where the static type of the value tells the result of checking it against [typeToCheck] already, see
 * [StaticTypeCheckResult.of].
 * @param typeOfValue the static type of the value; `null` if not known
 * @param typeToCheck the result of [validateTypeCheck]
 * @param reportAlwaysSucceeds whether a check that always succeeds is worth a warning
 * @return what was found, [StaticTypeCheckResult.Unknown] where one of the types is not known
 */
internal fun reportStaticResultOfTypeCheck(
    kind: TypeCheckKind,
    typeOfValue: BoundTypeReference?,
    typeToCheck: BoundTypeReference?,
    span: Span,
    diagnosis: Diagnosis,
    reportAlwaysSucceeds: (typeOfValue: BoundTypeReference, typeToCheck: BoundTypeReference) -> Boolean = { _, _ -> true },
): StaticTypeCheckResult {
    if (typeOfValue == null || typeToCheck == null) {
        return StaticTypeCheckResult.Unknown
    }

    val result = StaticTypeCheckResult.of(typeOfValue, typeToCheck)
    when (result) {
        is StaticTypeCheckResult.AlwaysSucceeds -> if (reportAlwaysSucceeds(typeOfValue, typeToCheck)) {
            diagnosis.typeCheckAlwaysSucceeds(kind, typeOfValue, typeToCheck, span)
        }
        is StaticTypeCheckResult.NeverSucceeds -> diagnosis.typeCheckNeverSucceeds(kind, typeOfValue, typeToCheck, result.reason, span)
        is StaticTypeCheckResult.Unknown -> {}
    }
    return result
}

/**
 * @return the type to check values against at runtime, for `is` and `as`; `null` if there is none to check against
 */
internal fun validateTypeCheck(fullTypeToCheck: BoundTypeReference): BoundTypeReference? {
    return fullTypeToCheck.takeUnless { it is ErroneousType }
}

/**
 * Whether checking a value of the type [typeOfValue] against [this] takes no more than the base type of the object:
 * [this] is a type without type arguments that is not nullable, any reference of [typeOfValue] is of a mutability
 * that fits, and no token can get forgotten. Then the check allocates nothing, see
 * `emerge.core.reflection.isInstanceOf`.
 */
private fun BoundTypeReference.isCheckedByBaseTypeAlone(typeOfValue: BoundTypeReference?): Boolean {
    if (this !is RootResolvedTypeReference || !arguments.isNullOrEmpty()) {
        return false
    }

    // if the type of the value is a type parameter, this is the mutability of its bound, and the mutability of the
    // type argument is assignable wherever that is
    val mutabilityOfValue = typeOfValue?.mutability ?: TypeMutability.READONLY
    if (!isOfConstClass && !mutabilityOfValue.isAssignableTo(mutability)) {
        return false
    }

    // What may be a token is no value of a type that cannot be one (see TokenRule), and whether an object may be
    // a token is up to its type arguments, too: a `Box<SystemClock>` is no `NonToken`. The base type says it all
    // where this type has no objection, where the value is known to be no token, and where the object has no
    // type arguments: it is of this very class then, and that has none.
    val objectsHaveNoTypeArguments = !baseType.kind.allowsSubtypes && baseType.typeParameters.isNullOrEmpty()
    return mayBeToken || typeOfValue?.mayBeToken == false || objectsHaveNoTypeArguments
}

/**
 * @return the overload of `emerge.core.reflection.isInstanceOf` whose second parameter is of the base type [typeParameterBaseType]
 */
private fun SoftwareContext.isInstanceOfFunction(typeParameterBaseType: BoundBaseType, parameterCount: Int): BoundFunction {
    val reflectPackage = getPackage(reflectionBaseType.canonicalName.packageName)
        ?: throw InternalCompilerError("reflect package not found!")

    val isInstanceFn = reflectPackage.getTopLevelFunctionOverloadSetsBySimpleName("isInstanceOf")
        .asSequence()
        .filter { it.parameterCount == parameterCount }
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
 * The runtime type that tells `emerge.core.reflection.isInstanceOf` the mutability of the reference to the value
 * being checked; objects don't know that. Where the type of the value is a type parameter, the mutability is
 * that of the type argument, known only at runtime.
 */
private fun SoftwareContext.reificationOfReferenceMutability(typeOfValue: BoundTypeReference?): IrType {
    val nonNullable = (typeOfValue as? NullableTypeReference)?.nested ?: typeOfValue
    if (nonNullable is GenericTypeReference) {
        return nonNullable.toBackendIr()
    }

    return IrSimpleTypeImpl(
        any.toBackendIr(),
        (typeOfValue?.mutability ?: TypeMutability.READONLY).toBackendIr(),
        isNullable = false,
    )
}

/**
 * @param typeOfValue the static type of [value]; `null` if not known, it is taken to be `read` then
 * @return an [IrExpression] that evaluates to `true` iff `value` is a value of the type [typeToCheck], and `false`
 * otherwise. For a type without type arguments that is not nullable, that is a check of the base type of the object.
 * For others, it is the subtype relation of the runtime, mutability included.
 */
internal fun buildInstanceOf(
    swCtx: SoftwareContext,
    value: IrTemporaryValueReference,
    typeToCheck: BoundTypeReference,
    typeOfValue: BoundTypeReference?,
): IrImplicitEvaluationExpression {
    val isInstanceFn: BoundFunction
    val typeTemporary: IrCreateTemporaryValue
    var referenceTypeTemporary: IrCreateTemporaryValue? = null
    val typeIsOwnedByThisCode: Boolean
    if (typeToCheck.isCheckedByBaseTypeAlone(typeOfValue)) {
        isInstanceFn = swCtx.isInstanceOfFunction(swCtx.reflectionBaseType, 2)
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
        isInstanceFn = swCtx.isInstanceOfFunction(swCtx.reflectionType, 3)
        val irTypeOfReifiedTypes = IrSimpleTypeImpl(
            swCtx.reflectionType.toBackendIr(),
            IrTypeMutability.IMMUTABLE,
            isNullable = false,
        )
        typeTemporary = IrCreateTemporaryValueImpl(
            IrReifiedTypeExpressionImpl(typeToCheck.toBackendIr(), irTypeOfReifiedTypes)
        )
        referenceTypeTemporary = IrCreateTemporaryValueImpl(
            IrReifiedTypeExpressionImpl(swCtx.reificationOfReferenceMutability(typeOfValue), irTypeOfReifiedTypes)
        )
        typeIsOwnedByThisCode = true
    }

    val isInstanceTemporary = IrCreateTemporaryValueImpl(
        IrStaticDispatchFunctionInvocationImpl(
            isInstanceFn.toBackendIr(),
            listOfNotNull(
                value,
                IrTemporaryValueReferenceImpl(typeTemporary),
                referenceTypeTemporary?.let(::IrTemporaryValueReferenceImpl),
            ),
            emptyMap(),
            isInstanceFn.returnType!!.toBackendIr(),
            null, // isInstanceOf is declared nothrow
        )
    )

    return IrImplicitEvaluationExpressionImpl(
        IrCodeChunkImpl(listOfNotNull(
            typeTemporary,
            referenceTypeTemporary,
            isInstanceTemporary,
            referenceTypeTemporary?.let(::IrDropStrongReferenceStatementImpl),
            IrDropStrongReferenceStatementImpl(typeTemporary).takeIf { typeIsOwnedByThisCode },
        )),
        IrTemporaryValueReferenceImpl(isInstanceTemporary),
    )
}

/**
 * @param typeOfValue the static type of [value], see [buildInstanceOf]
 * @return an [IrExpression] that evaluates to the `emerge.core.CastError` for a failed cast of [value] to [typeToCheck].
 * The error says what the value is and what [typeToCheck] is, so both types are reified here, also where
 * [buildInstanceOf] gets by with the base type. That is fine, this code only runs when the cast has failed.
 */
internal fun buildCastError(
    swCtx: SoftwareContext,
    value: IrTemporaryValueReference,
    typeToCheck: BoundTypeReference,
    typeOfValue: BoundTypeReference?,
): IrImplicitEvaluationExpression {
    val castErrorFn = swCtx.getPackage(swCtx.reflectionBaseType.canonicalName.packageName)
        ?.getTopLevelFunctionOverloadSetsBySimpleName(CAST_ERROR_FACTORY_FN_NAME)
        ?.singleOrNull()
        ?.overloads
        ?.singleOrNull()
        ?: throw InternalCompilerError("Could not unambiguously determine the function $CAST_ERROR_FACTORY_FN_NAME")
    check(castErrorFn.attributes.isDeclaredNothrow) {
        "$CAST_ERROR_FACTORY_FN_NAME must be nothrow, a failing cast has no landingpad for it"
    }

    val irTypeOfReifiedTypes = IrSimpleTypeImpl(
        swCtx.reflectionType.toBackendIr(),
        IrTypeMutability.IMMUTABLE,
        isNullable = false,
    )
    val typeTemporary = IrCreateTemporaryValueImpl(
        IrReifiedTypeExpressionImpl(typeToCheck.toBackendIr(), irTypeOfReifiedTypes)
    )
    val referenceTypeTemporary = IrCreateTemporaryValueImpl(
        IrReifiedTypeExpressionImpl(swCtx.reificationOfReferenceMutability(typeOfValue), irTypeOfReifiedTypes)
    )
    val castErrorTemporary = IrCreateTemporaryValueImpl(
        IrStaticDispatchFunctionInvocationImpl(
            castErrorFn.toBackendIr(),
            listOf(
                value,
                IrTemporaryValueReferenceImpl(typeTemporary),
                IrTemporaryValueReferenceImpl(referenceTypeTemporary),
            ),
            emptyMap(),
            castErrorFn.returnType!!.toBackendIr(),
            null, // declared nothrow, see above
        )
    )

    return IrImplicitEvaluationExpressionImpl(
        IrCodeChunkImpl(listOf(
            typeTemporary,
            referenceTypeTemporary,
            castErrorTemporary,
            IrDropStrongReferenceStatementImpl(referenceTypeTemporary),
            IrDropStrongReferenceStatementImpl(typeTemporary),
        )),
        IrTemporaryValueReferenceImpl(castErrorTemporary),
    )
}

/** `emerge.core.reflection.castErrorOf(Any?, Type, Type)` */
private const val CAST_ERROR_FACTORY_FN_NAME = "castErrorOf"

internal class IrBaseTypeReflectionExpressionImpl(
    override val baseType: IrBaseType,
    override val evaluatesTo: IrType,
) : IrBaseTypeReflectionExpression
