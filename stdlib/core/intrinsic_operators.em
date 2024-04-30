package emerge.core

export intrinsic operator fun unaryMinus(self: S32) -> S32

export intrinsic operator fun opPlus(self: S32, summand: S32) -> S32

export intrinsic operator fun opMinus(self: S32, operand: S32) -> S32

export intrinsic operator fun unaryMinus(self: SWord) -> SWord
export intrinsic operator fun opPlus(self: SWord, summand: SWord) -> SWord
export intrinsic operator fun opMinus(self: SWord, summand: SWord) -> SWord

export intrinsic operator fun opPlus(self: UWord, summand: UWord) -> UWord
export intrinsic operator fun opMinus(self: UWord, sommand: UWord) -> UWord
