package compiler.compiler.binding.type

import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.useValidModule
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldBeIn
import io.kotest.matchers.shouldBe
import java.util.concurrent.atomic.AtomicReference

/**
 * What the proofs in `type-system-proofs/theories` show of the model's unify, checked of the frontend's over the
 * types of [TypeGrid]: reflexivity (`FinalValues.reflexive_never_fails`), transitivity (`Transitivity.v`,
 * `Generics.transitivity_never_fails`), that instantiating type parameters with bindings within their bounds keeps
 * assignability (`Substitution.v`), and that unify finishes (the conjecture `unify_terminates` in `Conjectures.v`).
 * A violation is a divergence between the frontend and the model, or a counterexample to the conjecture.
 */
class UnificationPropertiesTests : FreeSpec({
    val types = TypeGrid.types

    fun List<String>.shouldBeNone() {
        withClue(take(100).joinToString("\n") + if (size > 100) "\n... ${size - 100} more" else "") {
            shouldBeEmpty()
        }
    }

    /** whether a is below b, of the types of [TypeGrid] by index; null where unify threw */
    val below: List<List<Boolean?>> = types.map { (_, a) ->
        types.map { (_, b) ->
            try {
                a.isBelow(b)
            } catch (e: Exception) {
                null
            }
        }
    }

    "unify doesn't throw" {
        types.indices.flatMap { i ->
            types.indices.mapNotNull { j ->
                if (below[i][j] != null) null else {
                    val e = runCatching { types[i].second.isBelow(types[j].second) }.exceptionOrNull()
                    "${types[i].first} to ${types[j].first}: ${e?.let { it::class.simpleName + " " + it.message }}"
                }
            }
        }.shouldBeNone()
    }

    "every type is below itself" {
        types.indices
            .filter { below[it][it] != true }
            .map { types[it].first }
            .shouldBeNone()
    }

    "assignability is transitive" {
        types.indices.flatMap { i ->
            types.indices.filter { below[i][it] == true }.flatMap { j ->
                types.indices
                    .filter { k -> below[j][k] == true && below[i][k] == false }
                    .map { k -> "${types[i].first} below ${types[j].first} below ${types[k].first}" }
            }
        }.shouldBeNone()
    }

    "the instantiations bind the type parameters within their bounds" {
        TypeGrid.instantiations.flatMap { (ctxStr, bindings) ->
            TypeGrid.ctxBounds.mapNotNull { (parameter, bound) ->
                val value = TypeGrid.swCtx.parseTypeIn("Ctx", parameter).instantiateAllParameters(bindings)
                val boundInstance = TypeGrid.swCtx.parseTypeIn("Ctx", bound).instantiateAllParameters(bindings)
                "in $ctxStr: $parameter = $value, not within $boundInstance".takeUnless { value.isBelow(boundInstance) }
            }
        }.shouldBeNone()
    }

    "instantiating type parameters within their bounds keeps assignability" {
        TypeGrid.instantiations.flatMap { (ctxStr, bindings) ->
            val instances = types.map { (_, t) -> runCatching { t.instantiateAllParameters(bindings) } }
            types.indices.flatMap { i ->
                types.indices.filter { below[i][it] == true }.mapNotNull { j ->
                    val a = instances[i].getOrNull()
                    val b = instances[j].getOrNull()
                    val result = if (a == null || b == null) null else runCatching { a.isBelow(b) }.getOrNull()
                    if (result == true) null else
                        "in $ctxStr: ${types[i].first} below ${types[j].first}, but not $a below $b" +
                            if (result == null) " (threw)" else ""
                }
            }
        }.shouldBeNone()
    }

    "unify finishes" - {
        // inheritance that isn't expansive, as ExpansiveInheritance.kt has it, but recursive through type arguments
        val swCtx = useValidModule("""
            interface A {}
            interface Ord<T> {}
            interface Cn<T> {}
            class K : Cn<Cn<in K>> {}
            class L<T> : Ord<L<T>> {}
            class S : Ord<Ord<in S>> {}
            class Ctx<F : Ord<in F>, G : Cn<in G>> {}
        """.trimIndent())

        val queries = listOf(
            // Kennedy and Pierce's example: a naive algorithm asks K below Cn<in K> again
            "K" to "Cn<in K>",
            "K" to "Cn<in Cn<in K>>",
            "Cn<Cn<in K>>" to "Cn<in K>",
            "Cn<in K>" to "K",
            "S" to "Ord<in S>",
            "S" to "Ord<in Ord<in S>>",
            "L<L<A>>" to "Ord<in L<L<A>>>",
            "L<A>" to "Ord<out L<A>>",
            "F" to "Ord<in F>",
            "G" to "Cn<in G>",
            "G" to "Cn<in Cn<in G>>",
            "K" to "G",
            "Cn<in K>" to "Cn<in G>",
        )

        "a goal that comes back to itself fails" {
            for ((assignee, target) in listOf("K" to "Cn<in K>", "Cn<Cn<in K>>" to "Cn<in K>", "S" to "Ord<in S>")) {
                withClue("$assignee to $target") {
                    swCtx.parseTypeIn("Ctx", assignee).isBelow(swCtx.parseTypeIn("Ctx", target)) shouldBe false
                }
            }
        }

        for ((assignee, target) in queries) {
            "$assignee to $target" {
                val a = swCtx.parseTypeIn("Ctx", assignee)
                val t = swCtx.parseTypeIn("Ctx", target)
                val outcome = AtomicReference<String>()
                val thread = Thread {
                    outcome.set(try {
                        if (a.isBelow(t)) "below" else "not below"
                    } catch (e: StackOverflowError) {
                        "stack overflow"
                    } catch (e: Throwable) {
                        "${e::class.simpleName} ${e.message}"
                    })
                }
                thread.isDaemon = true
                thread.start()
                thread.join(10_000)
                val result = outcome.get() ?: "didn't finish within 10s"
                "$assignee to $target: $result" shouldBeIn listOf("below", "not below").map { "$assignee to $target: $it" }
            }
        }
    }
})
