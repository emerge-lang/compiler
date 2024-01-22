package emerge.lang

intrinsic operator fun unaryMinus(self: Int) -> Int

intrinsic operator fun opPlus(self: Int, summand: Int) -> Int

intrinsic operator fun opMinus(self: Int, operand: Int) -> Int

intrinsic fun get<T>(self: readonly Array<out T>, index: Int) -> T

intrinsic fun set<T>(self: mutable Array<in T>, index: Int, value: T) -> Unit

intrinsic fun size(self: readonly Array<out readonly Any?>) -> Int

struct String {
    utf8Data: Array<Byte>
}