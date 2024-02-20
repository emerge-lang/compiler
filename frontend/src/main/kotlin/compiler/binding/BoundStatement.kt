package compiler.binding

import compiler.ast.Statement

interface BoundStatement<out AstNode : Statement> : BoundExecutable<AstNode> {
}