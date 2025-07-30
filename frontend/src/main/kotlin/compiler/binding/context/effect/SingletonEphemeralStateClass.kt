package compiler.binding.context.effect

abstract class SingletonEphemeralStateClass<State, Effect : SingletonEphemeralStateClass.SingletonEffect> :
    EphemeralStateClass<SingletonEphemeralStateClass.Subject, State, Effect> {
    final override fun getInitialState(subject: Subject): State = initialState

    abstract val initialState: State

    object Subject

    abstract class SingletonEffect(override val stateClass: SingletonEphemeralStateClass<*, *>) : SideEffect<Subject> {
        final override val subject = Subject
    }
}