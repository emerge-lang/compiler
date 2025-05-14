package compiler.compiler.binding.type

import compiler.ast.type.TypeReference
import compiler.binding.context.SoftwareContext
import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.lexCode
import compiler.lexer.Span
import compiler.parser.grammar.Type
import compiler.parser.grammar.rule.MatchingResult
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.assertions.fail
import io.kotest.matchers.Matcher
import io.kotest.matchers.MatcherResult

internal fun SoftwareContext.parseType(
    type: String,
    module: String = "testmodule",
    definedAt: StackTraceElement = Thread.currentThread().stackTrace[2]
): BoundTypeReference {
    val moduleCtx = getRegisteredModule(CanonicalElementName.Package(listOf(module)))
    val tokens = lexCode(addPackageDeclaration = false, code = type, invokedFrom = definedAt)
    val typeMatch = Type.match(tokens, 0)
        .sortedByDescending { it is MatchingResult.Success<*> }
        .filter { when (it) {
            is MatchingResult.Success<*> -> it.continueAtIndex == tokens.size - 1
            else -> true
        } }
        .firstOrNull()
    if (typeMatch == null) {
        fail("Failed to parse type")
    }
    if (typeMatch is MatchingResult.Error) {
        fail(typeMatch.diagnostic.toString())
    }
    check(typeMatch is MatchingResult.Success<TypeReference>)
    val boundType = moduleCtx.sourceFiles.first().context.resolveType(typeMatch.item)
    return boundType
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