package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.FunctionDeclaration
import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.Any
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference
import compiler.binding.type.Unit
import compiler.nullableOr
import compiler.parser.Reporting

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
class BoundFunction(
    val context: CTContext,
    val declaration: FunctionDeclaration,
    val parameters: BoundParameterList,
    val code: BoundExecutable<*>?
) {
    val declaredAt = declaration.declaredAt

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [FunctionDeclaration.receiverType] to resolve the ambiguity.
     */
    var receiverType: BaseTypeReference? = null
        private set

    val name: String = declaration.name.value

    /**
     * Implied modifiers. Operator functions often have an implied [FunctionModifier.READONLY]
     */
    val impliedModifiers: Set<FunctionModifier> = {
        // only operator functions have implied modifiers
        if (FunctionModifier.OPERATOR !in declaration.modifiers) {
            emptySet<FunctionModifier>()
        }

        when {
            name.startsWith("opUnary")                         -> setOf(FunctionModifier.READONLY)
            name.startsWith("op") && !name.endsWith("Assign")  -> setOf(FunctionModifier.READONLY)
            name == "rangeTo" || name == "contains"            -> setOf(FunctionModifier.READONLY)
            else                                               -> emptySet()
        }
    }()

    val modifiers = declaration.modifiers + impliedModifiers

    val parameterTypes: List<BaseTypeReference?>
        get() = declaration.parameters.types.map { it?.resolveWithin(context) }

    var returnType: BaseTypeReference? = null
        private set

    val isDeclaredPure: Boolean = FunctionModifier.PURE in declaration.modifiers

    /**
     * Whether this functions code is behaves in a pure way. Is null if that has not yet been determined (see semantic
     * analysis) or if the function has no body.
     */
    var isEffectivelyPure: Boolean? = null
        private set

    /**
     * Whether this function should be considered pure by other code using it. This is true if the function is
     * declared pure. If that is not the case the function is still considered pure if the declared
     * body behaves in a pure way.
     * This value is null if the purity was not yet determined; it must be non-null when semantic analysis is completed.
     * @see isDeclaredPure
     * @see isEffectivelyPure
     */
    val isPure: Boolean?
        get() = if (isDeclaredPure) true else isEffectivelyPure

    val isDeclaredPeadonly: Boolean = isDeclaredPure || FunctionModifier.READONLY in declaration.modifiers

    /**
     * Whether this functions code behaves in a readonly way. Is null if that has not yet been determined (see semantic
     * analysis) or if the function has no body.
     */
    var isEffectivelyReadonly: Boolean? = null
        private set

    /**
     * Whether this function should be considered readonly by other code using it. This is true if the function is
     * declared readonly or pure. If that is not the case the function is still considered readonly if the declared
     * body behaves in a readonly way.
     * This value is null if the purity was not yet determined; it must be non-null when semantic analysis is completed.
     * @see isDeclaredPure
     * @see isEffectivelyPure
     */
    val isReadonly: Boolean?
        get() = if (isDeclaredPeadonly || isDeclaredPure) true else isEffectivelyReadonly

    val fullyQualifiedName: String
        get() = (context.module?.name?.joinToString(".") ?: "<unknown module>") + "." + name

    fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        receiverType = declaration.receiverType?.resolveWithin(context)

        if (declaration.receiverType != null && receiverType == null) {
            reportings.add(Reporting.unknownType(declaration.receiverType!!))
        }

        // modifiers
        if (FunctionModifier.EXTERNAL in modifiers) {
            if (code != null) {
                reportings.add(Reporting.error("Functions declared as external must not declare a function body.", declaredAt))
            }
        }
        else if (code == null) {
            reportings.add(Reporting.error("No function body specified. Declare the function as external or declare a body.", declaredAt))
        }

        if (FunctionModifier.PURE in modifiers && FunctionModifier.READONLY in modifiers) {
            reportings.add(Reporting.info("The modifier readonly is superfluous: the function is also pure and pure implies readonly.", declaredAt))
        }

        // parameters
        reportings.addAll(parameters.semanticAnalysisPhase1(false))

        if (declaration.returnType != null) {
            returnType = declaration.returnType!!.resolveWithin(context)
            if (returnType == null) {
                reportings.add(Reporting.unknownType(declaration.returnType!!))
            }
        }

        // the codechunk has no semantic analysis phase 1

        return reportings
    }

    fun semanticAnalysisPhase2(): Collection<Reporting> {
        // TODO: detect recursion and issue error about cyclic type inference
        if (returnType == null) {
            if (this.code is BoundExpression<*>) {
                if (this.code.type == null) {
                    return setOf(Reporting.consecutive("Cannot determine type of function expression; thus cannot infer return type of function."))
                }

                this.returnType = this.code.type!!
            }
            else {
                throw InternalCompilerError("Semantic analysis phase 1 did not determine return type of function; cannot infer in phase 2 because the functions code is not an expression.")
            }
        }

        return emptySet()
    }

    fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (code != null) {
            if (returnType != null) {
                code.enforceReturnType(returnType!!)
            }

            reportings += code.semanticAnalysisPhase3()

            // readonly and purity checks
            val statementsReadingBeyondFunctionContext = code.findReadsBeyond(context)
            val statementsWritingBeyondFunctionContext = code.findWritesBeyond(context)

            isEffectivelyReadonly = statementsWritingBeyondFunctionContext.isEmpty()
            isEffectivelyPure = isEffectivelyReadonly!! && statementsReadingBeyondFunctionContext.isEmpty()

            if (isDeclaredPure) {
                if (!isEffectivelyPure!!) {
                    reportings.addAll(Reporting.purityViolations(statementsReadingBeyondFunctionContext, statementsWritingBeyondFunctionContext, this))
                }
                // else: effectively pure means effectively readonly
            }
            else if (isDeclaredPeadonly && !isEffectivelyReadonly!!) {
                reportings.addAll(Reporting.readonlyViolations(statementsWritingBeyondFunctionContext, this))
            }

            // assure all paths return or throw
            val isGuaranteedToTerminate = code.isGuaranteedToReturn nullableOr code.isGuaranteedToThrow
            if (isGuaranteedToTerminate == null) {
                throw InternalCompilerError("Could not determine whether function $this returns or throws on all executions paths")
            }

            if (!isGuaranteedToTerminate) {
                // if the function is declared to return Unit a return of Unit is implied and should be inserted by backends
                if (returnType == null || returnType!!.baseType !== Unit) {
                    reportings.add(Reporting.functionIsNotGuaranteedToTerminate(this))
                }
            }
        }

        return reportings
    }
}

/**
 * Given the invocation types `receiverType` and `parameterTypes` of an invocation site
 * returns the functions matching the types sorted by matching quality to the given
 * types (see [BaseTypeReference.isAssignableTo] and [BaseTypeReference.assignMatchQuality])
 *
 * In essence, this function is the function dispatching algorithm of the language.
 */
fun Iterable<BoundFunction>.filterAndSortByMatchForInvocationTypes(receiverType: BaseTypeReference?, parameterTypes: Iterable<BaseTypeReference?>): List<BoundFunction> =
    this
        // filter out the ones with incompatible receiver type
        .filter {
            // both null -> don't bother about the receiverType for now
            if (receiverType == null && it.receiverType == null) {
                return@filter true
            }
            // both must be non-null
            if (receiverType == null || it.receiverType == null) {
                return@filter false
            }

            return@filter receiverType.isAssignableTo(it.receiverType!!)
        }
        // filter by incompatible number of parameters
        .filter { it.declaration.parameters.parameters.size == parameterTypes.count() }
        // filter by incompatible parameters
        .filter { candidateFn ->
            parameterTypes.forEachIndexed { paramIndex, paramType ->
                val candidateParamType = candidateFn.parameterTypes[paramIndex] ?: Any.baseReference(candidateFn.context)
                if (paramType != null && !(paramType isAssignableTo candidateParamType)) {
                    return@filter false
                }
            }

            return@filter true
        }
        // now we can sort
        // by receiverType ASC, parameter... ASC
        .sortedWith(
            compareBy(
                // receiver type
                {
                    receiverType?.assignMatchQuality(it.receiverType!!) ?: 0
                },
                // parameters
                { candidateFn ->
                    var value: Int = 0
                    parameterTypes.forEachIndexed { paramIndex, paramType ->
                        value = paramType?.assignMatchQuality(candidateFn.parameterTypes[paramIndex] ?: Any.baseReference(candidateFn.context)) ?: 0
                        if (value != 0) return@forEachIndexed
                    }

                    value
                }
            )
        )