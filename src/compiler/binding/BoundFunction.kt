package compiler.binding

import compiler.ast.FunctionDeclaration
import compiler.binding.context.CTContext
import compiler.binding.type.Any
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
class BoundFunction(
    val context: CTContext,
    val declaration: FunctionDeclaration,

    val receiverType: BaseTypeReference?,
    val parameters: BoundParameterList,
    val returnType: BaseTypeReference?,
    val code: BoundCodeChunk?
) {
    val name: String = declaration.name.value
    val modifiers = declaration.modifiers

    val parameterTypes: List<BaseTypeReference?>
        get() = declaration.parameters.types.map { it?.resolveWithin(context) }
}

/**
 * Given the invocation types `receiverType` and `parameterTypes` of an invocation site
 * returns the functions matching the types sorted by matching quality to the given
 * types (see [BaseTypeReference.isAssignableTo] and [BaseTypeReference.assignMatchQuality])
 *
 * In essence, this function is the function dispatching algorithm of the language.
 */
fun Iterable<out BoundFunction>.filterAndSortByMatchForInvocationTypes(receiverType: BaseTypeReference?, parameterTypes: Iterable<out BaseTypeReference?>): List<BoundFunction> =
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