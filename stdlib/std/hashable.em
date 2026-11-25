package emerge.std

import emerge.core.utf8.codepoints
import emerge.core.safemath.{plusModulo, timesModulo}

export interface HashState<R> {
    export fn add(self: mut _, v: S8)
    export fn add(self: mut _, v: U8)
    export fn add(self: mut _, v: S16)
    export fn add(self: mut _, v: U16)
    export fn add(self: mut _, v: S32)
    export fn add(self: mut _, v: U32)
    export fn add(self: mut _, v: S64)
    export fn add(self: mut _, v: U64)
    export fn add(self: mut _, v: SWord)
    export fn add(self: mut _, v: UWord)
    export fn add(self: mut _, v: String)
    export get fn hashValue(self) -> R
}

export interface Hashable {
    export fn addTo(self, borrow hash: HashState<*>)
}

export interface HashAlgorithm<R> : NonToken {
    export fn newState(self) -> own HashState<R>
}

export fn hashWith<R>(self: Hashable, algo: HashAlgorithm<R>) -> R {
    state: mut HashState<R> = algo.newState()
    state.add(self)
    return state.hashValue
}

export class JavaLikeHashAlgorithm : HashAlgorithm<UWord> {
    export override fn newState(self) = JavaLikeHashState()
}

export class JavaLikeHashState : HashState<UWord> {
    private var value: UWord = 0

    export override fn add(self: mut _, v: S8) = self.add(v.toS64())
    export override fn add(self: mut _, v: U8) = self.add(v.toU64())
    export override fn add(self: mut _, v: S16) = self.add(v.toS64())
    export override fn add(self: mut _, v: U16) = self.add(v.toU64())
    export override fn add(self: mut _, v: S32) = self.add(v.toS64())
    export override fn add(self: mut _, v: U32) = self.add(v.toU64())
    export override fn add(self: mut _, v: S64) = self.add(v.asU64())
    export override fn add(self: mut _, v: U64) {
        if U64.max() == UWord.max().asU64() {
            self.add(v.asUWord())
        } else {
            self.add(v.logicalBitShiftRight(32).asUWord())
            self.add(v.asUWord())
        }
    }
    export override fn add(self: mut _, v: SWord) = self.add(v.asUWord())
    export override fn add(self: mut _, v: UWord) {
        set self.value = self.value.timesModulo(31 as UWord).plusModulo(v)
    }
    export override fn add(self: mut _, v: String) {
        self.add(v.utf8Data.size)
        foreach codepoint in v.codepoints() {
            self.add(codepoint)
        }
    }

    export override get fn hashValue(self) -> UWord = self.value
}

export fn add(self: mut HashState<*>, borrow v: Hashable) {
    v.addTo(self)
}