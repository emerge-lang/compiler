package compiler.binding.type

class UnboundTypeVariableException(val variable: TypeVariable) : RuntimeException("Missing binding for type variable $variable")