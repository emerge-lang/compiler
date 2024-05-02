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
}

export class U8 {
    private constructor {}
}

export class S16 {
    private constructor {}
}

export class U16 {
    private constructor {}
}

export class S32 {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> S32
    export intrinsic operator fn opPlus(self, summand: S32) -> S32
    export intrinsic operator fn opMinus(self, operand: S32) -> S32
}

export class U32 {
    private constructor {}
}

export class S64 {
    private constructor {}
}

export class U64 {
    private constructor {}
}

export class SWord {
    private constructor {}

    export intrinsic operator fn unaryMinus(self) -> SWord
    export intrinsic operator fn opPlus(self, summand: SWord) -> SWord
    export intrinsic operator fn opMinus(self, summand: SWord) -> SWord
}

export class UWord {
    private constructor {}

    export intrinsic operator fn opPlus(self, summand: UWord) -> UWord
    export intrinsic operator fn opMinus(self, summand: UWord) -> UWord
}

export class Bool {
    private constructor {}
}

export class Array<Element> {
    export size: UWord = init

    private constructor {}

    export intrinsic fn get(self: read _<out Element>, index: UWord) -> Element

    export intrinsic fn set(self: mut _<in Element>, index: UWord, value: Element) -> Unit

    export intrinsic fn size(self: read _) -> UWord
}
