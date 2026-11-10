package emerge.core

export class ArithmeticError : Error {
    private _message: String = init
    
    nothrow constructor {
        mixin ThrowableTrait(self._message)
    }
}