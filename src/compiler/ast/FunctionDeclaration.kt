package compiler.ast

import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.binding.BindingResult
import compiler.binding.BoundCodeChunk
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val modifiers: Set<FunctionModifier>,

    /**
     * The receiver type; is null if the declared function has no receiver.
     */
    val receiverType: TypeReference?,
    val name: IdentifierToken,
    val parameters: ParameterList,
    val returnType: TypeReference,
    val code: CodeChunk?
) : Declaration {
    fun bindTo(context: CTContext): BindingResult<BoundFunction> {
        val reportings = mutableListOf<Reporting>()

        // modifiers
        if (FunctionModifier.EXTERNAL in modifiers) {
            if (code != null) {
                reportings.add(Reporting.error("Functions declared as external must not declare a function body.", declaredAt))
            }
        }
        else if (code == null) {
            reportings.add(Reporting.error("No function body specified. Declare the function as external or declare a body.", declaredAt))
        }

        if (FunctionModifier.PURE in modifiers && FunctionModifier.READONLY in modifiers) {
            reportings.add(Reporting.info("The modifier readonly is superfluous: the function is also pure and pure implies readonly.", declaredAt))
        }

        // parameters
        val parametersBR = parameters.bindTo(context, false)
        reportings.addAll(parametersBR.reportings)

        // construct the code context from all the parameters
        val codeContext = MutableCTContext(context)
        codeContext.swCtx = context.swCtx

        parameters.parameters.forEach { param ->
            codeContext.addVariable(param)
        }

        // TODO: incorporate the READONLY, PURE and NOTHROW modifiers into codeContext

        val codeBR: BindingResult<BoundCodeChunk>?
        if (code != null) {
            codeBR = code.bindTo(context)
            reportings.addAll(codeBR.reportings)
        }
        else codeBR = null

        return BindingResult(
            BoundFunction(
                context,
                this,
                receiverBaseType,
                parametersBR.bound,
                returnBaseType,
                codeBR?.bound
            ),
            reportings
        )
    }
}