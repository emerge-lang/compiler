package io.github.tmarsteel.emerge.backend.llvm

import com.google.common.collect.MapMaker
import kotlin.reflect.KProperty
import kotlin.reflect.KProperty1
import kotlin.reflect.full.getExtensionDelegate
import kotlin.reflect.jvm.isAccessible

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
fun <T : Any> tackLateInitState() = LateInitStateTackDelegate<T>()

class StateTackDelegate<in R : Any, T>(private val computeInitial: R.() -> T) {
    private val data = MapMaker().weakKeys().makeMap<R, T>()

    operator fun getValue(thisRef: R, prop: KProperty<*>): T {
        return data.computeIfAbsent(thisRef, computeInitial)
    }

    operator fun setValue(thisRef: R, prop: KProperty<*>, value: T) {
        data[thisRef] = value
    }

    private fun reset(thisRef: R) {
        data.remove(thisRef)
    }

    companion object {
        fun <R : Any> reset(thisRef: R, prop: KProperty1<*, *>) {
            prop.isAccessible = true
            (prop.getExtensionDelegate() as StateTackDelegate<R, *>).reset(thisRef)
        }
    }
}

class LateInitStateTackDelegate<T : Any?> {
    private val data = MapMaker().weakKeys().makeMap<Any, T>()

    operator fun getValue(thisRef: Any, prop: KProperty<*>): T {
        return data[thisRef]
            ?: throw UninitializedPropertyAccessException("tacked lateinit ${thisRef::class.simpleName}::${prop.name}")
    }

    operator fun setValue(thisRef: Any, prop: KProperty<*>, value: T) {
        data[thisRef] = value
    }
}