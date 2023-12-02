package compiler.binding

import compiler.*
import compiler.ast.FunctionDeclaration
import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.Unit
import compiler.reportings.Reporting

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
class BoundDeclaredFunction(
    override val context: CTContext,
    val declaration: FunctionDeclaration,
    override val parameters: BoundParameterList,
    val code: BoundExecutable<*>?
) : BoundFunction() {
    override val declaredAt = declaration.declaredAt
    override val name: String = declaration.name.value

    override var receiverType: BaseTypeReference? = null
        private set

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

    override var returnType: BaseTypeReference? = null
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

            receiverType = declaration.receiverType?.resolveWithin(context)

            if (declaration.receiverType != null && receiverType == null) {
                reportings.add(Reporting.unknownType(declaration.receiverType))
            }

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

            // parameters
            reportings.addAll(parameters.semanticAnalysisPhase1(false))

            if (declaration.returnType != null) {
                returnType = declaration.returnType.resolveWithin(context)
                if (returnType == null) {
                    reportings.add(Reporting.unknownType(declaration.returnType))
                }
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

            return@getResult reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = mutableSetOf<Reporting>()

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
                    // if the function is declared to return Unit a return of Unit is implied and should be inserted by backends
                    // if this is a single-expression function (fun a() = 3), return is implied
                    if ((returnType == null || returnType!!.baseType !== Unit) && this.code !is BoundExpression<*>) {
                        reportings.add(Reporting.uncertainTermination(this))
                    }
                }
            }

            return@getResult reportings
        }
    }

}