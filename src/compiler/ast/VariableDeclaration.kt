package compiler.ast

import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.ast.expression.Expression
import compiler.binding.type.BaseTypeReference
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.BindingResult
import compiler.binding.BoundVariable
import compiler.binding.type.Any
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

open class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val isAssignable: Boolean,
    val assignExpression: Expression?
) : Declaration, Executable<BoundVariable> {
    /**
     * Determines and returns the type of the variable when initialized in the given context. If the type cannot
     * be determined due to semantic reportings, the closest guess is returned, even Any if there is absolutely no clue.
     */
    fun determineType(context: CTContext): BaseTypeReference? {
        val baseType = declaredType(context) ?: assignExpression?.determineType(context)

        return if (typeModifier == null) baseType else baseType?.modifiedWith(typeModifier)
    }

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
            reportings.add(Reporting.error("Cannot determine type for $selfType ${name.value}; neither type nor initializer is specified.", declaredAt))
        }

        // cannot resolve declared type
        val declaredType: BaseTypeReference? = declaredType(context)
        if (type != null && declaredType == null) {
            reportings.add(Reporting.unknownType(type))
        }
        if (declaredType != null) {
            reportings.addAll(declaredType.validate())
        }

        if (assignExpression != null) {
            reportings.addAll(assignExpression.validate(context))

            if (declaredType != null) {
                val initializerType = assignExpression.determineType(context)

                // if the initilizer type cannot be resolved the reporting is already done: assignExpression.validate
                // should have returned it; so: we dont care :)

                // discrepancy between assign expression and declared type
                if (initializerType != null) {
                    if (!(initializerType isAssignableTo declaredType)) {
                        reportings.add(Reporting.typeMismatch(declaredType, initializerType, assignExpression.sourceLocation))
                    }
                }
            }
        }

        val reportedType: BaseTypeReference? =
            if (type != null) declaredType else assignExpression?.determineType(context)

        return BindingResult(
            BoundVariable(
                context,
                this,
                reportedType
            ),
            reportings
        )
    }

    override fun modified(context: CTContext): CTContext {
        val existingVar = context.resolveVariable(name = name.value, onlyOwn = true)
        if (existingVar != null) {
            // this is a double declaration => do not change anything
            return context
        }

        val type = determineType(context) ?: Any.baseReference
        val newContext = MutableCTContext.deriveFrom(context)
        newContext.addVariable(this)
        return newContext
    }
}