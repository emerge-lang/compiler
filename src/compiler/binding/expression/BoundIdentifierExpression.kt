package compiler.binding.expression

import compiler.ast.Executable
import compiler.ast.expression.IdentifierExpression
import compiler.binding.BoundExecutable
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

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        if (referredType == ReferredType.VARIABLE) {
            for (contextInOwnHierarchy in context.hierarchy) {
                var variable = contextInOwnHierarchy.resolveVariable(identifier, true)
                if (variable === referredVariable) {
                    // variable has been declared within the boundary => the read is within the bondary
                    return emptySet() // no violation
                }

                // stop looking when we hit the boundary as going further would act outside of the boundary
                if (contextInOwnHierarchy === boundary) break
            }

            // the variable has not been found within the boundary => the read is outside of the boundary
            return setOf(this)
        }
        else {
            // TODO is reading type information of types declared outside the boundary considered impure?
            return emptySet() // no violation
        }
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        // this does not write by itself; writs are done by other statements
        return emptySet()
    }

    /** The kinds of things an identifier can refer to. */
    enum class ReferredType {
        VARIABLE,
        TYPENAME
    }
}
