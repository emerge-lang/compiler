package compiler.ast

import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.BindingResult
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

open class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val isAssignable: Boolean,
    val assignExpression: Expression<*>?
) : Declaration, Executable<BoundVariable> {
    override val sourceLocation = declaredAt

    fun declaredType(context: CTContext): BaseTypeReference? {
        if (type == null) return null
        val typeRef = if (typeModifier != null) type.modifiedWith(typeModifier) else type
        return typeRef.resolveWithin(context)
    }

    override fun bindTo(context: CTContext): BindingResult<BoundVariable> = bindTo(context, "variable")

    /**
     * @param context The context in which to validate
     * @param selfType What type to report this at; should be either `variable` or `parameter`
     */
    protected fun bindTo(context: CTContext, selfType: String): BindingResult<BoundVariable> {
        val reportings = mutableListOf<Reporting>()

        // double declaration
        val existingVariable = context.resolveVariable(name = name.value, onlyOwn = true)
        if (existingVariable != null) {
            reportings.add(Reporting.error("$selfType ${name.value} has already been defined in ${existingVariable.declaration.declaredAt.fileLineColumnText}", declaredAt))
        }

        // type-related stuff
        // unknown type
        if (assignExpression == null && type == null) {
            reportings.add(Reporting.error("Cannot determine type of $selfType ${name.value}; neither type nor initializer is specified.", declaredAt))
        }

        // cannot resolve declared type
        val declaredType: BaseTypeReference? = declaredType(context)
        if (type != null && declaredType == null) {
            reportings.add(Reporting.unknownType(type))
        }
        if (declaredType != null) {
            reportings.addAll(declaredType.validate())
        }

        val boundAssignExpression: BoundExpression<*>?
        if (assignExpression != null) {
            val assignExpressionBR = assignExpression.bindTo(context)
            reportings.addAll(assignExpressionBR.reportings)
            boundAssignExpression = assignExpressionBR.bound

            if (declaredType != null) {
                val initializerType = boundAssignExpression.type

                // if the initializer type cannot be resolved the reporting is already done by assignExpression.bindTo
                // should have returned it; so: we don't care :)

                // discrepancy between assign expression and declared type
                if (initializerType != null) {
                    if (!(initializerType isAssignableTo declaredType)) {
                        reportings.add(Reporting.typeMismatch(declaredType, initializerType, assignExpression.sourceLocation))
                    }
                }
            }

            // discrepancy between implied modifiers of assignExpression and type modifiers of this declaration
            val assignExprBaseType = boundAssignExpression.type?.baseType
            val assignExprTypeImpliedModifier = assignExprBaseType?.impliedModifier
            if (typeModifier != null && assignExprTypeImpliedModifier != null) {
                if (!(assignExprTypeImpliedModifier isAssignableTo typeModifier)) {
                    reportings.add(Reporting.error("Modifier $typeModifier not applicable to implied modifier $assignExprTypeImpliedModifier of $assignExprBaseType", declaredAt))
                }
            }
        }
        else boundAssignExpression = null

        val reportedBaseType = if (type != null) declaredType else boundAssignExpression?.type
        val reportedType = if (typeModifier == null) reportedBaseType else reportedBaseType?.modifiedWith(typeModifier)

        return BindingResult(
            BoundVariable(
                context,
                this,
                reportedType
            ),
            reportings
        )
    }
}