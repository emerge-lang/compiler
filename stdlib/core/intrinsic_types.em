package emerge.core

export class Unit {
    private constructor {}
}

export interface Any {}

export class Nothing {
    private constructor {}
}

export class F32 {
    private constructor {}
}

export class F64 {
    private constructor {}
}

export class S8 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S8
    export intrinsic operator fn negate(self) -> S8
}

export class U8 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U8
}

export class S16 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S16
    export intrinsic operator fn negate(self) -> S16
}

export class U16 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U16
}

export class S32 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S32
    export intrinsic operator fn negate(self) -> S32
    export intrinsic operator fn opPlus(self, summand: S32) -> S32
    export intrinsic operator fn opMinus(self, operand: S32) -> S32
}

export class U32 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U32
}

export class S64 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S64
    export intrinsic operator fn negate(self) -> S64
}

export class U64 {
    private constructor {}

    export intrinsic operator fn negate(self) -> U64
}

export class SWord {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> SWord
    export intrinsic operator fn negate(self) -> SWord
    export intrinsic operator fn opPlus(self, summand: SWord) -> SWord
    export intrinsic operator fn opMinus(self, summand: SWord) -> SWord
}

export class UWord {
    private constructor {}

    export intrinsic operator fn negate(self) -> UWord
    export intrinsic operator fn opPlus(self, summand: UWord) -> UWord
    export intrinsic operator fn opMinus(self, summand: UWord) -> UWord
}

export class Bool {
    private constructor {}

    export intrinsic operator fn negate(self) -> Bool
}

export class Array<Element> {
    export size: UWord = init

    private constructor {}

    export operator intrinsic fn get(self: read _<out Element>, index: UWord) -> Element

    export operator intrinsic fn set(self: mut _<in Element>, index: UWord, value: Element) -> Unit

    export intrinsic fn size(self: read _) -> UWord

    export intrinsic fn new<T>(size: UWord, initialValue: T) -> exclusive Array<T>
}

export interface Throwable {}
export interface Error : Throwable {}
export interface Exception : Throwable {}