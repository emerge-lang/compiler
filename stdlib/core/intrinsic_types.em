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
}

export class UWord {
    private constructor {}
}

export class Bool {
    private constructor {}
}

export class Array<Element> {
    private constructor {}

    export intrinsic fun get(self: readonly _<out Element>, index: UWord) -> Element

    export intrinsic fun set(self: mutable _<in Element>, index: UWord, value: Element) -> Unit

    export intrinsic fun size(self: readonly _) -> UWord
}
