package compiler.ast.expression

import compiler.lexer.Operator

class UnaryExpression(val operator: Operator, valueExpression: Expression): Expression