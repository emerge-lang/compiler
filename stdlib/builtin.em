package emerge.lang

external operator fun unaryMinus(self: Int) -> Int

external operator fun opPlus(self: Int, summand: Int) -> Int

external operator fun opMinus(self: Int, operand: Int) -> Int

external fun get<T>(self: readonly Array<out T>, index: Int) -> T

external fun set<T>(self: mutable Array<in T>, index: Int, value: T) -> Unit

external fun size(self: readonly Array<out readonly Any?>) -> Int

struct String {
    utf8Data: Array<Byte>
}