package emerge.core

export class ArithmeticError : Error {
    ref private _message: const String = init
    
    constructor {
        mixin ThrowableTrait(self._message)
    }
}