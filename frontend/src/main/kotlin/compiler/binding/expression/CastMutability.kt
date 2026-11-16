package compiler.binding.expression

import compiler.ast.type.TypeMutability
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.forbiddenCast

/**
 * An object doesn't know the mutability of the references to it, so no check at runtime can make a `read`
 * reference a `mut` one. Of the value itself, a cast can only keep or weaken the mutability (`x: read Any`,
 * `x as read Foo`), not strengthen it (`x as mut Foo`), and `own` is never the target of a cast.
 *
 * This is checked here where the target says its mutability. Where it is a type parameter (`x as T`), the
 * mutability is that of the type argument, and the check at runtime compares it with the mutability of the
 * reference (see [buildInstanceOf]).
 *
 * The mutability in type arguments (`x as Array<mut Foo>`) is no concern of this: objects know their type
 * arguments, mutability included, and the check at runtime covers it.
 *
 * @param target the type as written in the cast, never nullable just for the cast being `as?`
 * @param source the type of the value being cast
 */
internal fun BoundCastExpression.validateCastMutability(
    target: BoundTypeReference,
    source: BoundTypeReference,
    diagnosis: Diagnosis,
) {
    if (target.isInherentlyConst) {
        return
    }

    val reportAt = declaration.toType.span ?: declaration.span
    if (target.mutability == TypeMutability.OWN) {
        diagnosis.forbiddenCast(this, "Cannot cast to an own type: a cast cannot tell whether there are other references to the value.", reportAt)
    } else if (!source.mutability.isAssignableTo(target.mutability)) {
        diagnosis.forbiddenCast(
            this,
            "Cannot cast a ${source.mutability.keyword.text} value to a ${target.mutability.keyword.text} type: an object doesn't know the mutability of the references to it, so a cast can only keep or weaken it.",
            reportAt,
        )
    }
}

internal val BoundTypeReference.isInherentlyConst: Boolean
    get() = when (this) {
        is RootResolvedTypeReference -> baseType.isConst
        is NullableTypeReference -> nested.isInherentlyConst
        is BoundTypeArgument -> type.isInherentlyConst
        else -> false
    }
