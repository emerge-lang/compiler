package emerge.core.range

export interface Iterable<T> {
    export fn asRange(capture self) -> own InputRange<T>
}