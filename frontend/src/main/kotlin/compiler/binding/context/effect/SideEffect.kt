package compiler.binding.context.effect

interface SideEffect<out Subject : Any> {
    val subject: Subject
    val effectClass: SideEffectClass<*, *, *>
}