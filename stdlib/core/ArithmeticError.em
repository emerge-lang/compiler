package emerge.core

export class ArithmeticError : Error {
    private _message: const String = init
    
    constructor {
        mixin ThrowableTrait(self._message)
    }
}