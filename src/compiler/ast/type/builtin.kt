package compiler.ast.type

import ModuleMatcher
import compiler.InternalCompilerError
import compiler.ast.FunctionDeclaration
import compiler.ast.context.CTContext
import compiler.ast.context.MutableCTContext
import compiler.ast.context.Module
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.SourceContentAwareSourceLocation
import compiler.lexer.SourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence

/*
 * This file contains raw definitions of the builtin types.
 * Actual operations on these types are defined in the source
 * language in the stdlib as external functions with receiver.
 * The actual implementations are defined within the stdlib
 * package.
 */

val Any = object : BuiltinType("Any") {}

val Unit = object : BuiltinType("Unit", Any) {}

val Number = object : BuiltinType("Number", Any) {}

val Decimal = object : BuiltinType("Float", Number) {}

val Integer = object : BuiltinType("Int", Number) {}


/**
 * A BuiltinType is defined in the ROOT package. All instances created of this object
 * are automagically available in the root package (take a look at the source of [Module]
 * to see how that is achieved)
 */
abstract class BuiltinType(override val simpleName: String, vararg superTypes: BaseType) : BaseType {
    override final val fullyQualifiedName = simpleName

    override final val superTypes: Set<BaseType> = superTypes.toSet()

    override final val defaultReference = TypeReference(fullyQualifiedName, false, impliedModifier)

    /**
     * BaseTypes do not define anything themselves. All of that is defined in source language in the
     * stdlib and implementation is provided from elsewhere, probably platform-specific.
     */
    final override fun resolveMemberFunction(name: String) = emptySet<FunctionDeclaration>()

    companion object {
        /**
         * A [Context] that holds all instances of [BuiltinType]; updates dynamically whenever an instance of
         * [BuiltinType] is created.
         */
        val Context: CTContext = MutableCTContext()

        init {
            // parse builtin type operator definitions

        }
    }

    init {
        (Context as MutableCTContext).addBaseType(this)
    }
}

private fun parseFromClasspath(path: String, module: Module) {
    val sourceode = BuiltinType.javaClass.getResource(path).readText().lines()

    val sourceDescriptor = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "classpath://" + path
        override val sourceLines = sourceode
    }
    val matchResult = ModuleMatcher(module.name).tryMatch(TokenSequence(lex(sourceDescriptor).toList()))
    if (matchResult.result == null) {
        throw InternalCompilerError("Failed to parse compiler internal source")
    }
    return matchResult.result!!.includeInto(module.context)
}