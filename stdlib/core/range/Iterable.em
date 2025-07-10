package emerge.core.range

export interface Iterable<T> {
    export fn asRange(capture self) -> exclusive InputRange<T>
}