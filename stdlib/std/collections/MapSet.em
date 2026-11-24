package emerge.std.collections

export class MapSet<Element : const Equatable<Element>, MapT : Map<Element, Unit>> : Set<Element> {
    private map: mut MapT = init

    export override operator fn contains(self, borrow element: Element) = self.map.contains(element)

    export override fn add(self: mut _, element: Element) -> Bool {
        return isNull(self.map.setAtIndex(element, Unit.instance()))
    }

    export override fn remove(self: mut _, borrow element: Element) -> Bool {
        return not isNull(self.map.remove(element))
    }

    export fn newHashSet<E : const Hashable & Equatable<E>>(algorithm: HashAlgorithm<UWord>) -> MapSet<E, HashMap<E, Unit>> {
        return MapSet(HashMap::<E, Unit>(algorithm))
    }
}