package compiler.ast.expression

import compiler.ast.Bindable
import compiler.binding.expression.BoundExpression
import compiler.lexer.SourceLocation

interface Expression<out BoundType : BoundExpression<*>> : Bindable<BoundType> {
    val sourceLocation: SourceLocation
}

// TODO: source location, maybe Range<SourceLocation>?