package emerge.core

export interface Throwable {}
export interface Error : Throwable {}

export interface StackTraceElement {
    export fn toString(self) -> String
}

export class FilledStackTraceElement : StackTraceElement {
    export instructionPointer: UWord = init
    export procedureName: String? = init
    export fileName: String? = init
    export lineNumber: U32 = init

    override fn toString(self) -> String {
        var str: const _ = " at "
        if not isNull(self.procedureName) {
            set str = str + self.procedureName!!
        } else {
            set str = str + "??"
        }

        if not isNull(self.fileName) {
            set str = str + " in " + self.fileName!! + ":" + self.lineNumber.toString()
        }

        set str = str + " (" + self.instructionPointer.toString() + ")"

        return str
    }
}

export class ErrorStackTraceElement : StackTraceElement {
    export errorMessage: String = init
    override fn toString(self) -> const String = "    ... backtrace error: " + self.errorMessage
}
