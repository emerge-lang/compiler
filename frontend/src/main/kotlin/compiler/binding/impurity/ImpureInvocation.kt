package compiler.binding.impurity

import compiler.InternalCompilerError
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundInvocationExpression

data class ImpureInvocation(val invocation: BoundInvocationExpression, val functionToInvoke: BoundFunction) :
    Impurity {
    override val span = invocation.declaration.span
    override val kind = when (functionToInvoke.purity) {
        BoundFunction.Purity.PURE -> throw InternalCompilerError("Invoking a pure function cannot possibly be considered impure")
        BoundFunction.Purity.READONLY -> Impurity.ActionKind.READ
        BoundFunction.Purity.MODIFYING -> Impurity.ActionKind.MODIFY
    }
    override fun describe(): String = "invoking ${functionToInvoke.purity} function ${functionToInvoke.name}"
}