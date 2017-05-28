package compiler.binding

import compiler.ast.VariableDeclaration
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BaseTypeReference
import compiler.parser.Reporting

/**
 * Describes the presence/avaiability of a (class member) variable or (class member) value in a context.
 * Refers to the original declaration and contains an override type.
 */
class BoundVariable(
    override val context: CTContext,
    override val declaration: VariableDeclaration,
    val initializerExpression: BoundExpression<*>?
) : BoundExecutable<VariableDeclaration>
{
    val typeModifier = declaration.typeModifier

    val isAssignable: Boolean = declaration.isAssignable

    val name: String = declaration.name.value

    /**
     * The base type reference; null if not determined yet or if it cannot be determined due to semantic errors.
     */
    var type: BaseTypeReference? = null
        private set

    fun semanticAnalysisPhase1() = semanticAnalysisPhase1("variable")

    fun semanticAnalysisPhase1(selfType: String): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // type-related stuff
        // unknown type
        if (declaration.initializerExpression == null && declaration.type == null) {
            reportings.add(Reporting.error("Cannot determine type of $selfType $name; neither type nor initializer is specified.", declaration.declaredAt))
        }

        // cannot resolve declared type
        val declaredType: BaseTypeReference? = resolveDeclaredType(context)
        if (declaration.type != null && declaredType == null) {
            reportings.add(Reporting.unknownType(declaration.type))
        }
        if (declaredType != null) {
            type = declaredType
            reportings.addAll(declaredType.validate())
        }

        if (initializerExpression != null) {
            reportings.addAll(initializerExpression.semanticAnalysisPhase1())
        }

        return reportings
    }

    fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        if (initializerExpression != null) {

            reportings.addAll(initializerExpression.semanticAnalysisPhase2())

            // verify compatibility declared type <-> initializer type
            if (type != null) {
                val initializerType = initializerExpression.type

                // if the initializer type cannot be resolved the reporting is already done and
                // should have returned it; so: we don't care :)

                // discrepancy between assign expression and declared type
                if (initializerType != null) {
                    if (!(initializerType isAssignableTo type!!)) {
                        reportings.add(Reporting.typeMismatch(type!!, initializerType, declaration.initializerExpression!!.sourceLocation))
                    }
                }
            }

            // discrepancy between implied modifiers of initializerExpression and type modifiers of this declaration
            val assignExprBaseType = initializerExpression.type?.baseType
            val assignExprTypeImpliedModifier = assignExprBaseType?.impliedModifier
            if (typeModifier != null && assignExprTypeImpliedModifier != null) {
                if (!(assignExprTypeImpliedModifier isAssignableTo typeModifier)) {
                    reportings.add(Reporting.error("Modifier $typeModifier not applicable to implied modifier $assignExprTypeImpliedModifier of $assignExprBaseType", declaration.declaredAt))
                }
            }
        }

        // infer the type
        if (type == null) {
            val assignExprType = initializerExpression?.type
            type = if (typeModifier == null) assignExprType else assignExprType?.modifiedWith(typeModifier)
        }

        return reportings
    }

    private fun resolveDeclaredType(context: CTContext): BaseTypeReference? {
        with(declaration) {
            if (type == null) return null
            val typeRef = if (typeModifier != null) type.modifiedWith(typeModifier) else type
            return typeRef.resolveWithin(context)
        }
    }
}