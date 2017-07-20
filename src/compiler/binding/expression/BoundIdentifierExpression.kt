package compiler.binding.expression

import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseType
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression
) : BoundExpression<IdentifierExpression> {
    val identifier: String = declaration.identifier.value

    override val type: BaseTypeReference?
        get() = when(referredType) {
            ReferredType.VARIABLE -> referredVariable?.type
            ReferredType.TYPENAME -> referredBaseType?.baseReference?.invoke(context)
            null -> null
        }

    override var isReadonly: Boolean? = null
        private set

    /** What this expression refers to; is null if not known */
    var referredType: ReferredType? = null
        private set

    /** The variable this expression refers to, if it does (see [referredType]); otherwise null. */
    var referredVariable: BoundVariable? = null
        private set

    /** The base type this expression referes to, if it does (see [referredType]); otherwise null. */
    var referredBaseType: BaseType? = null
        private set

    override fun readsBeyond(boundary: CTContext): Boolean {
        if (referredType == ReferredType.VARIABLE) {
            context.hierarchy.forEach { contextInOwnHierarchy ->
                var variable = contextInOwnHierarchy.resolveVariable(identifier, true)
                if (variable === referredVariable) {
                    // variable has been declared within the boundary => the read is within the bondary
                    return@readsBeyond false
                }

                // stop looking when we hit the boundary as going further would act outside of the boundary
                if (contextInOwnHierarchy === boundary) return@forEach
            }

            // the variable has not been found within the boundary => the read is outside of the boundary
            return true
        }
        else {
            // TODO is reading type information of types declared outside the boundary considered impure?
            return false
        }
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // attempt variable
        val variable = context.resolveVariable(identifier)

        if (variable != null) {
            referredType = ReferredType.VARIABLE
            referredVariable = variable
        }
        else {
            var type: BaseType? = context.resolveDefinedType(identifier)
            if (type == null) {
                reportings.add(Reporting.undefinedIdentifier(declaration))
            }
            else {
                this.referredBaseType = type
                this.referredType = ReferredType.TYPENAME
            }
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // attempt a variable
        val variable = context.resolveVariable(identifier)
        if (variable != null) {
            referredVariable = variable
            referredType = ReferredType.VARIABLE
        }
        else {
            reportings.add(Reporting.error("Cannot resolve variable $identifier", declaration.sourceLocation))
        }

        // TODO: attempt to resolve type; expression becomes of type "Type/Class", ... whatever, still to be defined

        return reportings
    }

    /** The kinds of things an identifier can refer to. */
    enum class ReferredType {
        VARIABLE,
        TYPENAME
    }
}
