package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.ast.type.Any
import compiler.ast.type.BaseTypeReference
import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

interface Expression {

    val sourceLocation: SourceLocation

    /**
     * Determines and returns the type of this expression when evaluated in the given context. If the type cannot
     * be determined due to semantic reportings, a guess may be returned if it is sufficiently close to the actual type.
     * Otherwise, null should be returned.
     */
    fun determineType(context: CTContext): BaseTypeReference? = null // TODO: remove workaround when possible

    /**
     * Validates this expression within the given context.
     *
     * @return Any reportings about the validated code
     */
    fun validate(context: CTContext): Collection<Reporting> = emptySet() // TODO: remove workaround when possible
}

// TODO: source location, maybe Range<SourceLocation>?