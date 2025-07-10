package compiler.binding

import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.binding.expression.BoundInvocationExpression
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.accessorCapturesSelf
import compiler.diagnostic.accessorContractViolation
import compiler.diagnostic.accessorNotPure

sealed interface AccessorKind {
    /**
     * The type of the virtual member variable defined by this accessor, as defined in the accessor declaration.
     */
    fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference?

    fun validateContract(accessorFn: BoundDeclaredFunction, diagnosis: Diagnosis)

    data object Read : AccessorKind {
        override fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference? {
            return accessorFnOfKind.returnType
        }

        override fun validateContract(
            accessorFn: BoundDeclaredFunction,
            diagnosis: Diagnosis,
        ) {
            accessorFn.validateCommonContractAspects(diagnosis)

            with (accessorFn) {
                if (parameters.parameters.size != 1) {
                    diagnosis.accessorContractViolation(
                        declaration,
                        "Getters must declare exactly one parameter, which has to be `${BoundParameterList.RECEIVER_PARAMETER_NAME}`",
                        if (parameters.parameters.isEmpty()) declaredAt else parameters.parameters.drop(1)
                            .first().declaration.span,
                    )
                } else if (!declaresReceiver) {
                    diagnosis.accessorContractViolation(
                        declaration,
                        "The only parameter to getters has to be `${BoundParameterList.RECEIVER_PARAMETER_NAME}`",
                        parameters.parameters.single().declaration.span,
                    )
                }

                parameters.declaredReceiver?.let { receiverParam ->
                    receiverParam.typeAtDeclarationTime?.mutability?.let { receiverMutability ->
                        if (receiverMutability != TypeMutability.READONLY) {
                            diagnosis.accessorContractViolation(
                                declaration,
                                "Getters must act on ${TypeMutability.READONLY.keyword.text} objects, this one expects a ${receiverMutability.keyword.text} object",
                                receiverParam.declaration.span,
                            )
                        }
                    }
                }
            }
        }
    }

    data object Write : AccessorKind {
        override fun extractMemberType(accessorFnOfKind: BoundFunction): BoundTypeReference? {
            return accessorFnOfKind.parameters.parameters
                .drop(1)
                .firstOrNull()
                ?.typeAtDeclarationTime
        }

        override fun validateContract(
            accessorFn: BoundDeclaredFunction,
            diagnosis: Diagnosis,
        ) {
            accessorFn.validateCommonContractAspects(diagnosis)

            with(accessorFn) {
                if (parameters.parameters.size != 2) {
                    diagnosis.accessorContractViolation(
                        declaration,
                        "Setters have to take exactly two parameters. First, the object to modify (`${BoundParameterList.RECEIVER_PARAMETER_NAME}`), and the new value for the member variable second",
                        parameters.parameters.drop(2).firstOrNull()?.declaration?.span ?: declaredAt,
                    )
                } else if (!declaresReceiver) {
                    diagnosis.accessorContractViolation(
                        declaration,
                        "Setters have to take a `${BoundParameterList.RECEIVER_PARAMETER_NAME}` parameter",
                        parameters.parameters.firstOrNull()?.declaration?.span ?: declaredAt,
                    )
                }

                parameters.declaredReceiver?.let { receiverParam ->
                    receiverParam.typeAtDeclarationTime?.mutability?.let { receiverMutability ->
                        if (receiverMutability != TypeMutability.MUTABLE) {
                            diagnosis.accessorContractViolation(
                                declaration,
                                "Setters must act on ${TypeMutability.MUTABLE.keyword.text} objects, this one expects a ${receiverMutability.keyword.text} object",
                                receiverParam.declaration.type?.span ?: receiverParam.declaration.span,
                            )
                        }
                    }
                }

                if (returnType?.equals(functionRootContext.swCtx.unit.baseReference) == false) {
                    diagnosis.accessorContractViolation(
                        declaration,
                        "Setters must return `${functionRootContext.swCtx.unit.canonicalName}`",
                        declaration.parsedReturnType?.span ?: declaredAt,
                    )
                }
            }
        }
    }
}

object SetterDisambiguationBehavior : BoundInvocationExpression.DisambiguationBehavior {
    override fun shouldDisambiguateOnParameter(
        candidate: BoundFunction,
        parameter: BoundParameter,
        parameterIndex: UInt,
    ): Boolean {
        // only disambiguate on the receiver param, not on any other
        return parameter === candidate.parameters.declaredReceiver
    }
}

private fun BoundDeclaredFunction.validateCommonContractAspects(diagnosis: Diagnosis) {
    parameters.declaredReceiver?.let { receiverParam ->
        if (receiverParam.ownershipAtDeclarationTime != VariableOwnership.BORROWED) {
            diagnosis.accessorCapturesSelf(this, receiverParam)
        }
    }

    if (!BoundFunction.Purity.PURE.contains(purity)) {
        diagnosis.accessorNotPure(this)
    }
}