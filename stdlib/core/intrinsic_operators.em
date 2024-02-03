package emerge.core

intrinsic operator fun unaryMinus(self: Int) -> Int

intrinsic operator fun opPlus(self: Int, summand: Int) -> Int

intrinsic operator fun opMinus(self: Int, operand: Int) -> Int

intrinsic operator fun unaryMinus(self: iword) -> iword
intrinsic operator fun opPlus(self: iword, summand: iword) -> iword
intrinsic operator fun opMinus(self: iword, summand: iword) -> iword

intrinsic operator fun opPlus(self: uword, summand: uword) -> uword
intrinsic operator fun opMinus(self: uword, sommand: uword) -> uword

intrinsic fun get<T>(self: readonly Array<out T>, index: Int) -> T

intrinsic fun set<T>(self: mutable Array<in T>, index: Int, value: T) -> Unit

intrinsic fun size(self: readonly Array<out readonly Any?>) -> Int
