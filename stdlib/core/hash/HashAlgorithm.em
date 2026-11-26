package emerge.core.hash

import emerge.core.utf8.codepoints
import emerge.core.safemath.{plusModulo, timesModulo}
import emerge.core.hash.{Hashable, HashState}

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

    export override fn addRaw(self: mut _, borrow v: UWord) {
        set self.value = self.value.timesModulo(31 as UWord).plusModulo(v)
    }

    export override get fn hashValue(self) -> UWord = self.value
}