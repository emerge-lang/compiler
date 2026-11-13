package emerge.platform

import emerge.core.reflection.ReflectionBaseType
import emerge.std.Printable
import emerge.std.io.PrintStream

class S8Box : Printable {
    value: S8 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

// holds an array when it is referenced as one of the supertypes of Array, e.g. Any or Iterable.
// It is a token class as the array may hold tokens.
token class ArrayBox {
    value: Array<out Any?> = init
}

class U8Box : Printable {
    value: U8 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class S16Box : Printable {
    value: S16 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class U16Box : Printable {
    value: U16 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class S32Box : Printable {
    value: S32 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class U32Box : Printable {
    value: U32 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class S64Box : Printable {
    value: S64 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class U64Box : Printable {
    value: U64 = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class F32Box {
    value: F32 = init
}

class F64Box {
    value: F64 = init
}

class SWordBox : Printable {
    value: SWord = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class UWordBox : Printable {
    value: UWord = init

    export override fn printTo(self, borrow stream: mut PrintStream) {
        self.value.printTo(stream)
    }
}

class BoolBox {
    value: Bool = init
}

class ReflectionBaseTypeBox {
    value: ReflectionBaseType = init
}