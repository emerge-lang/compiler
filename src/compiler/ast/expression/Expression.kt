package compiler.ast.expression

import compiler.ast.context.CTContext
import compiler.ast.type.Any
import compiler.ast.type.TypeReference

interface Expression {

    /**
     * Determines and returns the type of this expression when evaluated in the given context. If the type cannot
     * be determined due to semantic errors, the closest guess is returned, even Any if there is absolutely no clue.
     */
    fun determinedType(context: CTContext): TypeReference = Any.defaultReference // TODO: remove workaround when possible
}

// TODO: source location, maybe Range<SourceLocation>?