package emerge.core

export interface Throwable {}
export interface Error : Throwable {}

export class StackTraceElement {
    export address: UWord = init
    export procedureName: String = init
}
