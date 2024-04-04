package emerge.core

export intrinsic operator fun unaryMinus(self: Int) -> Int

export intrinsic operator fun opPlus(self: Int, summand: Int) -> Int

export intrinsic operator fun opMinus(self: Int, operand: Int) -> Int

export intrinsic operator fun unaryMinus(self: iword) -> iword
export intrinsic operator fun opPlus(self: iword, summand: iword) -> iword
export intrinsic operator fun opMinus(self: iword, summand: iword) -> iword

export intrinsic operator fun opPlus(self: uword, summand: uword) -> uword
export intrinsic operator fun opMinus(self: uword, sommand: uword) -> uword

export intrinsic fun get<T>(self: readonly Array<out T>, index: Int) -> T

export intrinsic fun set<T>(self: mutable Array<in T>, index: Int, value: T) -> Unit

export intrinsic fun size(self: readonly Array<out readonly Any?>) -> uword
