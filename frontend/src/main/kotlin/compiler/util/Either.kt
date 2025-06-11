package compiler.util

sealed interface Either<out This, out That> {
    class This<This, That>(val value: This) : Either<This, That>
    class That<This, That>(val value: That) : Either<This, That>
}