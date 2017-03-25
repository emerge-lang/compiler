package compiler.ast

import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation
import compiler.parser.Reporting

class FunctionDeclaration(
    override val declaredAt: SourceLocation,
    val modifiers: Set<FunctionModifier>,
    val receiverType: TypeReference?,
    val name: IdentifierToken,
    val parameters: ParameterList,
    val returnType: TypeReference,
    val code: CodeChunk?
) : Declaration {
    fun validate(context: CTContext): Collection<Reporting> {
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
            reportings.add(Reporting.info("The readonly modifier is obsolete because pure implies readonly.", declaredAt))
        }

        // receiver type
        val receiverBaseType = receiverType?.resolveWithin(context)
        if (receiverType != null && receiverBaseType == null) {
            reportings.add(Reporting.unknownType(receiverType))
        }

        // parameters
        reportings.addAll(parameters.validate(context, false))

        // return type
        val returnBaseType = returnType.resolveWithin(context)
        if (returnBaseType == null) {
            reportings.add(Reporting.unknownType(returnType))
        }

        // construct the code context from all the parameters
        val codeContext = MutableCTContext(context)
        codeContext.swCtx = context.swCtx

        parameters.parameters.forEach { param ->
            codeContext.addVariable(param)
        }

        // TODO: incorporate the READONLY, PURE and NOTHROW modifiers into codeContext

        if (code != null) {
            reportings.addAll(code.validate(codeContext))
        }

        return reportings
    }
}