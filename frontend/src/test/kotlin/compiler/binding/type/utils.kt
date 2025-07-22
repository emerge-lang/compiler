package compiler.compiler.binding.type

import compiler.binding.context.SoftwareContext
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.lexCode
import compiler.lexer.Span
import compiler.parser.grammar.BracedTypeArguments
import compiler.parser.grammar.Type
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.Rule
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.assertions.fail
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult

private fun <T : Any> SoftwareContext.parse(
    snippet: String,
    grammar: Rule<T>,
): T {
    val invokedFrom = Thread.currentThread().stackTrace[3]
    val tokens = lexCode(addPackageDeclaration = false, code = snippet, invokedFrom = invokedFrom)
    val match = grammar.match(tokens, 0)
        .sortedByDescending { it is MatchingResult.Success<*> }
        .filter { when (it) {
            is MatchingResult.Success<*> -> it.continueAtIndex == tokens.size - 1
            else -> true
        } }
        .firstOrNull()
    if (match == null) {
        fail("Failed to parse type")
    }
    if (match is MatchingResult.Error) {
        fail(match.diagnostic.toString())
    }
    check(match is MatchingResult.Success<T>)

    return match.item
}

internal fun SoftwareContext.parseType(
    type: String,
    module: String = "testmodule",
): BoundTypeReference {
    val astType = parse(type, Type)
    val moduleCtx = getRegisteredModule(CanonicalElementName.Package(module.split('.')))
    val boundType = moduleCtx.sourceFiles.first().context.resolveType(astType)
    return boundType
}

internal fun SoftwareContext.parseTypeArgument(
    typeArgument: String,
    module: String = "testmodule",
    parameter: BoundTypeParameter? = null,
): BoundTypeArgument {
    val astArg = parse("<$typeArgument>", BracedTypeArguments).arguments.single()
    val moduleCtx = getRegisteredModule(CanonicalElementName.Package(module.split('.')))
    val boundArg = moduleCtx.sourceFiles.first().context.resolveTypeArgument(astArg, parameter)
    return boundArg
}

internal fun beAssignableTo(target: BoundTypeReference) = object : Matcher<BoundTypeReference> {
    override fun test(value: BoundTypeReference): MatcherResult {
        val result = value.evaluateAssignabilityTo(target, Span.UNKNOWN)
        val reasonPart = result?.reason ?: "no reason available"
        return object : MatcherResult {
            override fun passed() = result == null
            override fun failureMessage() = "$value should be assignable to $target, but isn't; $reasonPart"
            override fun negatedFailureMessage() = "$value should not be assignable to $target"
        }
    }
}