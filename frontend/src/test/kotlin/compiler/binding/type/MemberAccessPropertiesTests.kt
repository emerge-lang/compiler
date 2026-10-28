package compiler.compiler.binding.type

import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.instantiateAllParametersForWriting
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty

/**
 * Member access in generic code: what is read through a reference `H<y>`, y mentioning the type parameters of `Ctx`,
 * instantiated for bindings of those, is above what is read through `H<y>` instantiated, the reference at run time;
 * and what is written, instantiated, fits what the reference at run time takes. With `MemberAccess.v` and
 * `MemberIntersections.v` for the reference at run time, member access in generic code is sound (coverage #11).
 */
class MemberAccessPropertiesTests : FreeSpec({
    val swCtx = TypeGrid.swCtx

    val members = listOf(
        "X", "X?", "mut X", "read X", "const X", "X!", "mut X?",
        "Box<X>", "Box<out X>", "Box<in X?>", "Box<mut X>", "Box<X!>", "Box<X>?",
        "A & X", "A? & X", "mut A & X", "X & B", "Box<X> & B", "Box<out X>? & A?",
    ).map { it to swCtx.parseTypeIn("H", it) }

    val arguments = TypeGrid.types.map { it.first }.filterNot { it.startsWith("exclusive Nothing") }
    val references = arguments.flatMap { a -> listOf("", "out ", "in ").map { v -> "H<$v$a>" } }
        .mapNotNull { r -> runCatching { r to swCtx.parseTypeIn("Ctx", r) }.getOrNull() }

    /** what a value of the type reads as: an in-variant type argument as `read Any?` */
    fun read(t: BoundTypeReference): BoundTypeReference = when {
        t is BoundTypeArgument -> if (t.variance == TypeVariance.IN) swCtx.parseType("read Any?") else t.type
        t is NullableTypeReference && t.nested is BoundTypeArgument -> NullableTypeReference(read(t.nested))
        else -> t
    }

    /** what the type takes: an out-variant type argument nothing but `exclusive Nothing` */
    fun taken(t: BoundTypeReference): BoundTypeReference = when {
        t is BoundTypeArgument -> if (t.variance == TypeVariance.OUT) swCtx.parseType("exclusive Nothing") else t.type
        t is NullableTypeReference && t.nested is BoundTypeArgument -> NullableTypeReference(taken(t.nested))
        else -> t
    }

    fun List<String>.shouldBeNone() {
        withClue(take(60).joinToString("\n") + if (size > 60) "\n... ${size - 60} more" else "") {
            shouldBeEmpty()
        }
    }

    "the grid has references" {
        check(references.size > 100) { references.size }
    }

    "what is read in generic code, instantiated, is above what is read at run time" {
        TypeGrid.instantiations.flatMap { (ctxStr, bindings) ->
            references.flatMap { (refStr, ref) ->
                val runtimeRef = runCatching { ref.instantiateAllParameters(bindings) }.getOrNull()
                    ?: return@flatMap listOf("in $ctxStr: $refStr threw")
                members.mapNotNull { (memberStr, member) ->
                    try {
                        val static = read(member.instantiateAllParameters(ref.inherentTypeBindings)).instantiateAllParameters(bindings)
                        val runtime = read(member.instantiateAllParameters(runtimeRef.inherentTypeBindings))
                        "in $ctxStr: $memberStr of $refStr reads $runtime at run time, not below $static"
                            .takeUnless { runtime.isBelow(static) }
                    } catch (e: Exception) {
                        "in $ctxStr: $memberStr of $refStr: ${e::class.simpleName} ${e.message}"
                    }
                }
            }
        }.shouldBeNone()
    }

    "what is written in generic code, instantiated, fits what is written at run time" {
        TypeGrid.instantiations.flatMap { (ctxStr, bindings) ->
            references.flatMap { (refStr, ref) ->
                val runtimeRef = ref.instantiateAllParameters(bindings)
                members.mapNotNull { (memberStr, member) ->
                    try {
                        val static = taken(member.instantiateAllParametersForWriting(ref.inherentTypeBindings)).instantiateAllParameters(bindings)
                        val runtime = taken(member.instantiateAllParametersForWriting(runtimeRef.inherentTypeBindings))
                        "in $ctxStr: $memberStr of $refStr takes $static, at run time only $runtime"
                            .takeUnless { static.isBelow(runtime) }
                    } catch (e: Exception) {
                        "in $ctxStr: $memberStr of $refStr: ${e::class.simpleName} ${e.message}"
                    }
                }
            }
        }.shouldBeNone()
    }
})
