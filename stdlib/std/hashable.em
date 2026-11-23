package emerge.std

import emerge.core.utf8.StringCodepointsRange

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
    export fn addTo(self, borrow hash: HashState)
}

export interface HashAlgorithm<R> {
    export fn newState(self) -> HashState<R>
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
    export override fn add(self: mut _, v: U8)
    export override fn add(self: mut _, v: S16)
    export override fn add(self: mut _, v: U16)
    export override fn add(self: mut _, v: S32)
    export override fn add(self: mut _, v: U32)
    export override fn add(self: mut _, v: S64)
    export override fn add(self: mut _, v: U64)
    export override fn add(self: mut _, v: SWord)
    export override fn add(self: mut _, v: UWord)
    export override fn add(self: mut _, v: String) {
        add(v.utf8data.size)
        foreach codepoint in StringCodepointsRange(v) {
            add(codepoint)
        }
    }

    export get fn hashValue(self) -> UWord = self.value
}

export fn add(self: mut HashState<*>, borrow v: Hashable) {
    v.addTo(self)
}