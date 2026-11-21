package emerge.std

import emerge.core.utf8.StringCodepointsRange

export interface HashState<R> {
    export fn add(self: mut _, v: S8) = self.add(v.toS64())
    export fn add(self: mut _, v: U8) = self.add(v.toU64())
    export fn add(self: mut _, v: S16) = self.add(v.toS64())
    export fn add(self: mut _, v: U16) = self.add(v.toU64())
    export fn add(self: mut _, v: S32) = self.add(v.toS64())
    export fn add(self: mut _, v: U32) = self.add(v.toU64())
    export fn add(self: mut _, v: S64)
    export fn add(self: mut _, v: U64)
    export fn add(self: mut _, v: SWord) = self.add(v.toS64())
    export fn add(self: mut _, v: UWord) = self.add(v.toU64())
    export fn add(self: mut _, v: String) {
        add(v.utf8data.size)
        for codepoint in StringCodepointsRange(v) {
            add(codepoint)
        }
    }
    export fn add(self: mut _, borrow v: Hashable) {
        v.addTo(self)
    }

    export get fn hashValue(self) -> R
}

export interface Hashable {
    export fn addTo(self, borrow hash: HashState)
}

export interface HashAlgorithm<R> {
    export fn newState(self) -> HashState<R>
}

export fn hashWith<R>(self: Hashable, algo: HashAlgorithm<R>) -> R {
    var state = algo.newState()
    state.add(self)
    return state.hashValue
}