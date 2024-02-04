package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import kotlin.reflect.KProperty

/*
Defining a whole new AST for another pass is considerable work, and for each
new tree structure over the AST all the forward-reference handling has to be done all over.
Long-Term this work pays off in performance. But for prototyping the backend and even figuring out
what i really need, i just want to "tack" some state onto some objects.
 */

fun <R : Any, T> tackLazyVal(compute: R.() -> T) = ComputedLazyTackDelegate(compute)

class ComputedLazyTackDelegate<in R : Any, out T>(
    private val compute: R.() -> T,
) {
    /**
     * This needs to be an IdentityWeakMap. Not in the default SDK, and its hard
     * to compose one. See https://stackoverflow.com/questions/22910375/combo-of-identityhashmap-and-weakhashmap
     */
    private val data = MapMaker().weakKeys().makeMap<R, T>()

    operator fun getValue(thisRef: R, prop: KProperty<*>): T {
        return data.computeIfAbsent(thisRef, compute)
    }
}

fun <R : Any, T> tackState(computeInitial: R.() -> T) = StateTackDelegate<R, T>(computeInitial)

class StateTackDelegate<in R : Any, T : Any?>(private val computeInitial: R.() -> T) {
    private val data = MapMaker().weakKeys().makeMap<R, T>()

    operator fun getValue(thisRef: R, prop: KProperty<*>): T {
        return data.computeIfAbsent(thisRef, computeInitial)
    }

    operator fun setValue(thisRef: R, prop: KProperty<*>, value: T) {
        data[thisRef] = value
    }
}