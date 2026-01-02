package emerge.core

export class ArithmeticError : Error {
    private _message: String = init
    
    constructor {
        mixin ThrowableTrait(self._message)
    }
}