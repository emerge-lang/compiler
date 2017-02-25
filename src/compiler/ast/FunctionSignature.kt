package compiler.ast

import compiler.ast.type.TypeReference

/** A function signature as used by function literals and defined functions alike */
class FunctionSignature (
    /** Parameters; Null values indicate non-specified parameters */
    val parameterTypes: List<TypeReference?>,
    val returnType: TypeReference
)