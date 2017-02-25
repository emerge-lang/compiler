package compiler.ast.expression

import compiler.lexer.Operator

class UnaryExpression(val operator: Operator, val valueExpression: Expression): Expression