package emerge.platform

import emerge.core.reflection.ReflectionBaseType

// TODO: change all builtin numeric-types and the boxes to be subtypes of const Any
// TODO: change all boxes to use owned member vars

class S8Box {
    ref value: const S8 = init
}

class U8Box {
    ref value: const U8 = init
}

class S16Box {
    ref value: const S16 = init
}

class U16Box {
    ref value: const U16 = init
}

class S32Box {
    ref value: const S32 = init
}

class U32Box {
    ref value: const U32 = init
}

class S64Box {
    ref value: const S64 = init
}

class U64Box {
    ref value: const U64 = init
}

class F32Box {
    ref value: const F32 = init
}

class F64Box {
    ref value: const F64 = init
}

class SWordBox {
    ref value: const SWord = init
}

class UWordBox {
    ref value: const UWord = init
}

class BoolBox {
    ref value: const Bool = init
}

class ReflectionBaseTypeBox {
    ref value: const ReflectionBaseType = init
}