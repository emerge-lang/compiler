package emerge.core.range

export interface Iterable<T> {
    fn asRange(capture self) -> mut InputRange<T>
}