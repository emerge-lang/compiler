package emerge.std.collections

export class MapSet<Element : const Equatable<Element>> : Set<Element> {
    private map: mut Map<Element, Unit> = init

    export override operator fn contains(self, borrow element: Element) = self.map.contains(element)

    export override fn add(self: mut _, element: Element) -> Bool {
        return isNull(self.map.setAtIndex(element, Unit.instance()))
    }

    export override fn remove(self: mut _, borrow element: Element) -> Bool {
        return not isNull(self.map.remove(element))
    }

    export fn newHashSet<E : const Hashable & Equatable<Element>>() -> MapSet<Element> = MapSet(HashMap())
}