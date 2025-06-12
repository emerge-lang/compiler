package compiler.util

class CircularDependencyException(val involvedElement: Any) : RuntimeException("Circular dependency detected: $involvedElement")