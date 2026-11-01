package compiler.diagnostic

import compiler.ast.FunctionDeclaration
import compiler.binding.basetype.InheritedBoundMemberFunction
import compiler.diagnostic.rendering.CellBuilder

class IncompatibleReturnTypeOnOverrideDiagnostic(
    val override: FunctionDeclaration,
    val superFunction: InheritedBoundMemberFunction,
    private val base: ValueNotAssignableDiagnostic,
) : Diagnostic(
    Severity.ERROR,
    "The return type of this override is not a subtype the overridden functions return type: ${base.simplifiedMessage ?: base.reason}",
    base.span,
) {
    context(builder: CellBuilder)    
    override fun renderBody() {
        with(builder) {
            horizontalLayout {
                column {
                    text("overridden function:")
                    text("overridden function returns:")
                    text("override returns:")
                }
                column {
                    append(superFunction.supertypeMemberFn.canonicalName.quote())
                    appendLineBreak()

                    append(base.targetType.quote())
                    appendLineBreak()

                    append(base.sourceType.quote())
                }
            }
            super.renderBody()
        }
    }
}