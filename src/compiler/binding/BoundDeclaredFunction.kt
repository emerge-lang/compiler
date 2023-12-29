package compiler.binding

import compiler.*
import compiler.ast.FunctionDeclaration
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.BuiltinUnit
import compiler.reportings.Reporting

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
class BoundDeclaredFunction(
    override val context: CTContext,
    val declaration: FunctionDeclaration,
    override val typeParameters: List<BoundTypeParameter>,
    override val parameters: BoundParameterList,
    val code: BoundExecutable<*>?
) : BoundFunction() {
    override val declaredAt = declaration.declaredAt
    override val name: String = declaration.name.value

    override val receiverType: ResolvedTypeReference?
        get() = parameters.declaredReceiver?.type

    override val declaresReceiver = parameters.declaredReceiver != null

    /**
     * Implied modifiers. Operator functions often have an implied [FunctionModifier.READONLY]
     */
    val impliedModifiers: Set<FunctionModifier> = run {
        // only operator functions have implied modifiers
        if (FunctionModifier.OPERATOR !in declaration.modifiers) {
            emptySet<FunctionModifier>()
        }

        when {
            name.startsWith("opUnary")                                -> setOf(FunctionModifier.READONLY)
            name.startsWith("op") && !name.endsWith("Assign") -> setOf(FunctionModifier.READONLY)
            name == "rangeTo" || name == "contains"                           -> setOf(FunctionModifier.READONLY)
            else                                                              -> emptySet()
        }
    }

    override val modifiers = declaration.modifiers + impliedModifiers

    override var returnType: ResolvedTypeReference? = null
        private set

    val isDeclaredPure: Boolean = FunctionModifier.PURE in declaration.modifiers

    /**
     * Whether this functions code is behaves in a pure way. Is null if that has not yet been determined (see semantic
     * analysis) or if the function has no body.
     */
    var isEffectivelyPure: Boolean? = null
        private set

    val isDeclaredReadonly: Boolean = FunctionModifier.READONLY in declaration.modifiers

    /**
     * Whether this functions code behaves in a readonly way. Is null if that has not yet been determined (see semantic
     * analysis) or if the function has no body.
     */
    var isEffectivelyReadonly: Boolean? = null
        private set

    override val isPure: Boolean?
        get() = if (isDeclaredPure) true else isEffectivelyPure

    override val isReadonly: Boolean?
        get() = if (isDeclaredReadonly || isDeclaredPure) true else isEffectivelyReadonly

    override val isGuaranteedToThrow: Boolean?
        get() = try {
                throwOnCycle(this) {
                    return@throwOnCycle code?.isGuaranteedToThrow
                }
            } catch (ex: EarlyStackOverflowException) {
                false
            }

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableSetOf<Reporting>()

            reportings.addAll(parameters.semanticAnalysisPhase1())

            // modifiers
            if (FunctionModifier.EXTERNAL in modifiers) {
                if (code != null) {
                    reportings.add(Reporting.illegalFunctionBody(declaration))
                }
            } else if (code == null) {
                reportings.add(Reporting.missingFunctionBody(declaration))
            }

            if (FunctionModifier.PURE in modifiers && FunctionModifier.READONLY in modifiers) {
                reportings.add(
                    Reporting.inefficientModifiers(
                        "The modifier readonly is superfluous: the function is also pure and pure implies readonly.",
                        declaredAt
                    )
                )
            }

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase1).forEach(reportings::addAll)
            reportings.addAll(parameters.semanticAnalysisPhase1(false))

            if (declaration.returnType != null) {
                returnType = context.resolveType(declaration.returnType)
            }

            this.code?.semanticAnalysisPhase1()?.let(reportings::addAll)

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            val reportings = mutableSetOf<Reporting>()

            try {
                throwOnCycle(this) {
                    this.code?.semanticAnalysisPhase2()?.let(reportings::addAll)
                }
            } catch (ex: EarlyStackOverflowException) {
                throw CyclicTypeInferenceException()
            } catch (ex: CyclicTypeInferenceException) {
                reportings.add(
                    Reporting.typeDeductionError(
                        "Cannot infer the return type of function $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                        declaredAt
                    )
                )
            }

            if (returnType == null) {
                if (this.code is BoundExpression<*>) {
                    this.returnType = this.code.type
                } else {
                    reportings += Reporting.consecutive("Cannot infer return type because function body is not an expression", declaredAt)
                }
            }

            receiverType?.let {
                it.validate(TypeUseSite.InUsage(it.sourceLocation)).let(reportings::addAll)
            }
            parameterTypes.forEach {
                it?.validate(TypeUseSite.InUsage(it.sourceLocation))?.let(reportings::addAll)
            }
            returnType?.let {
                val returnTypeUseSite = TypeUseSite.OutUsage(
                    declaration.returnType?.declaringNameToken?.sourceLocation
                        ?: this.declaredAt
                )
                reportings.addAll(it.validate(returnTypeUseSite))
            }
            typeParameters.forEach {
                reportings.addAll(it.semanticAnalysisPhase2())
                if (it.variance != TypeVariance.UNSPECIFIED) {
                    reportings.add(Reporting.varianceOnFunctionTypeParameter(it))
                }
            }


            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = mutableSetOf<Reporting>()

            typeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)

            if (code != null) {
                if (returnType != null) {
                    code.setExpectedReturnType(returnType!!)
                }

                reportings += code.semanticAnalysisPhase3()

                // readonly and purity checks
                val statementsReadingBeyondFunctionContext = try {
                    throwOnCycle(this) {
                        code.findReadsBeyond(context)
                    }
                } catch (ex: EarlyStackOverflowException) {
                    emptySet()
                }
                val statementsWritingBeyondFunctionContext = try {
                    throwOnCycle(this) {
                        code.findWritesBeyond(context)
                    }
                } catch (ex: EarlyStackOverflowException) {
                    emptySet()
                }

                isEffectivelyReadonly = statementsWritingBeyondFunctionContext.isEmpty()
                isEffectivelyPure = isEffectivelyReadonly!! && statementsReadingBeyondFunctionContext.isEmpty()

                if (isDeclaredPure) {
                    if (!isEffectivelyPure!!) {
                        reportings.addAll(
                            Reporting.purityViolations(
                                statementsReadingBeyondFunctionContext,
                                statementsWritingBeyondFunctionContext,
                                this
                            )
                        )
                    }
                    // else: effectively pure means effectively readonly
                } else if (isDeclaredReadonly && !isEffectivelyReadonly!!) {
                    reportings.addAll(Reporting.readonlyViolations(statementsWritingBeyondFunctionContext, this))
                }

                // assure all paths return or throw
                val isGuaranteedToTerminate = code.isGuaranteedToReturn nullableOr code.isGuaranteedToThrow

                if (!isGuaranteedToTerminate) {
                    val localReturnType = returnType
                    // if the function is declared to return Unit a return of Unit is implied and should be inserted by backends
                    // if this is a single-expression function (fun a() = 3), return is implied
                    if (localReturnType == null || (localReturnType is RootResolvedTypeReference && localReturnType.baseType !== BuiltinUnit && this.code !is BoundExpression<*>)) {
                        reportings.add(Reporting.uncertainTermination(this))
                    }
                }
            }

            return@getResult reportings
        }
    }

}