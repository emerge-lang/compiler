package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.ast.type.FunctionModifier
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.type.Any
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference
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
    val code: BoundCodeChunk?
) {
    val declaredAt = declaration.declaredAt

    /**
     * The type of the receiver. Is null if the declared function has no receiver or if the declared receiver type
     * could not be resolved. See [FunctionDeclaration.receiverType] to resolve the ambiguity.
     */
    var receiverType: BaseTypeReference? = null
        private set

    val name: String = declaration.name.value
    val modifiers = declaration.modifiers

    val parameterTypes: List<BaseTypeReference?>
        get() = declaration.parameters.types.map { it?.resolveWithin(context) }

    var returnType: BaseTypeReference? = null
        private set

    fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        receiverType = declaration.receiverType?.resolveWithin(context)

        if (declaration.receiverType != null && receiverType == null) {
            reportings.add(Reporting.unknownType(declaration.receiverType))
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

        returnType = declaration.returnType.resolveWithin(context)
        if (returnType == null) {
            reportings.add(Reporting.unknownType(declaration.returnType))
        }

        // the codechunk has no semantic analysis phase 1

        return reportings
    }

    fun semanticAnalysisPhase2(): Collection<Reporting> {
        // TODO: if the function is a () = expression, infer the return type
        return emptySet()
    }

    // TODO: incorporate the READONLY, PURE and NOTHROW modifiers into codeContext
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