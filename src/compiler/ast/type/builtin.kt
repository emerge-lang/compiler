package compiler.ast.type

import compiler.ast.FunctionDeclaration
import compiler.ast.context.CTContext
import compiler.ast.context.MutableCTContext
import compiler.parseFromClasspath

/*
 * This file contains raw definitions of the builtin types.
 * Actual operations on these types are defined in the source
 * language in the stdlib as external functions with receiver.
 * The actual implementations are defined within the stdlib
 * package.
 */

val Any = object : BuiltinType("Any") {}

val Unit = object : BuiltinType("Unit", Any) {}

val Number = object : BuiltinType("Number", Any) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}

val Float = object : BuiltinType("Float", Number) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}

val Int = object : BuiltinType("Int", Number) {
    override val impliedModifier = TypeModifier.IMMUTABLE
}


/**
 * A BuiltinType is defined in the ROOT package.
 */
abstract class BuiltinType(override val simpleName: String, vararg superTypes: BaseType) : BaseType {
    override final val fullyQualifiedName = simpleName

    override final val superTypes: Set<BaseType> = superTypes.toSet()

    override final val reference
        get() = TypeReference(fullyQualifiedName, false, impliedModifier)

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
            (Context as MutableCTContext).let {
                it.addBaseType(Any)
                it.addBaseType(Unit)
                it.addBaseType(Number)
                it.addBaseType(Float)
                it.addBaseType(Int)
            }

            // parse builtin type operator definitions
            // parseFromClasspath("builtin.dt").includeInto(Context as MutableCTContext)
        }
    }
}