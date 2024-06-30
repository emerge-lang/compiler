package emerge.core

export interface Throwable {}
export interface Error : Throwable {}

export class StackTraceElement {
    export address: UWord = init
    export procedureName: String = init
    
    export fn toString(self) -> String {
        return "  at " + self.procedureName + " (" + self.address.toString() + ")"
    }
}
