package compiler.binding

import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement,
    val returnType: BaseTypeReference?
) : BoundExecutable<ReturnStatement>