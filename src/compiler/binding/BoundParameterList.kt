package compiler.binding

import compiler.ast.ParameterList
import compiler.binding.context.CTContext

class BoundParameterList(
    val context: CTContext,
    val declaration: ParameterList,
    val parameters: List<BoundParameter>
)

typealias BoundParameter = BoundVariable