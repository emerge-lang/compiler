package emerge.std.collections

import emerge.core.safemath.plusModulo

export class HashMap<Key : const Hashable & Equatable<Key>, Value> {
    private var buckets: Array<mut ArrayList<mut MapEntry<Key, Value>>?> = Array::new(16, null)
    private var hashAlgorithm: HashAlgorithm<UWord> = init
    private var maxBucketSize = 4
    private var version: UWord = 0
    private var _size: UWord = 0

    export operator fn setAtIndex(self: mut _, index: Key, value: Value) -> Value? {
        return self.storeEntry(MapEntry(key, value), true)
    }

    private fn storeEntry(entry: MapEntry<Key, Value>, grow: Bool) -> Value? {
        hash = entry.key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(2.pow(self.buckets.size) - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            for bucketEntry in bucket {
                if bucketEntry.key.equals(bucket.key) {
                    if bucketEntry.isSameInstanceAs(entry) {
                        return bucketEntry.value
                    }

                    previousValue = bucketEntry.value
                    self.bumpVersion()
                    set entry.value = value
                    return previousValue
                }
            }

            if grow and bucket.size > self.maxBucketSize {
                self.growAndRehash()
                return storeEntry(entry, false)
            }
        } else {
            bucket = ArrayList()
            self.buckets[bucketIndex] = bucket
        }

        self.bumpVersion()
        bucket.add(MapEntry(key, value))
        set self._size = self._size + 1
        return null
    }

    export override operator fn getAtIndex(self, borrow index: Key) -> Value? {
        return getEntry(key)?.value
    }

    export override operator fn contains(self, borrow index: Key) {
        return not isNull(getEntry(key))
    }

    private fn getEntry(self, borrow key: Key) -> MapEntry<Key, Value>? {
        hash = key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(2.pow(self.buckets.size) - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            for entry in bucket {
                if entry.key.equals(key) {
                    return entry
                }
            }
        }
        
        return null
    }

    export override fn remove(self: mut _, key: Key) -> Value? {
        hash = entry.key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(2.pow(self.buckets.size) - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            for entryIndex in 0..<bucket.size {
                entry = bucket[entryIndex]
                if entry.key.equals(key) {
                    bucket.removeAtIndex(entryIndex)
                    set self.size = self.size - 1
                    return entry.value
                }
            }
        }

        return null
    }

    export fun asRange(self) -> HashMapRange<Key, Value> = HashMapRange(self)

    export get fn size(self) -> UWord = self._size
    
    private fn growAndRehash(self: mut _) {
        self.bumpVersion()
        var oldBuckets = self.buckets
        self.buckets = Array::new(self.buckets.size * 2, null)
        for bucket in oldBuckets  {
            if isNull(bucket) {
                continue
            }
            for entry in bucket {
                self.storeEntry(entry, false)
            }
        }
    }

    private fn bumpVersion(self: mut _) {
        set self.version = self.version.plusModulo(1)
    }
}

export class HashMapRange<Key : const Hashable & Equatable<Key>, Value> : SizedRange<out read MapEntry<Key, Value>> & BidirectionalRange<out read MapEntry<Key, Value>> {
    private map: HashMap<Key, Value> = init
    private atVersion: UWord = self.map.version
    private var frontBucketIndex: UWord = 0
    private var indexInFrontBucket: UWord = 0
    private var backBucketIndexPlus1: UWord = self.map.buckets.size
    private var indexInBackBucketPlus1: UWord = if self.map.buckets.size > 0 {
        self.map.buckets[$ - 1].size
    } else {
        1
    }

    private nothrow constructor {}

    private fn checkNotModified(self) {
        if map.version != atVersion {
            throw ConcurrentModificationError()
        }
    }

    export override get fn front(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.frontBucketIndex >= self.map.buckets.size {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.frontBucketIndex]
        if self.indexInFrontBucket >= bucket.size {
            throw EmptyRangeException()
        }

        return bucket[self.indexInFrontBucket]
    }

    export override fn popFront(self: mut _) {
        if self.frontBucketIndex >= self.map.buckets.size {
            return
        }

        bucket = self.map.buckets[self.frontBucketIndex]
        if self.indexInFrontBucket >= bucket.size {
            set self.frontBucketIndex = self.frontBucketIndex + 1
            set self.indexInFrontBucket = 0
            return
        }

        set self.indexInFrontBucket = self.indexInFrontBucket + 1
    }

    export override get fn back(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.backBucketIndexPlus1 == 0 || self.indexInBackBucketPlus1 == 0 {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.backBucketIndexPlus1 - 1]
        return bucket[self.indexInBackBucketPlus1 - 1]
    }

    export override fn popBack(self: mut _) {
        self.checkNotModified()

        if self.indexInBackBucketPlus1 > 1 {
            set self.indexInBackBucketPlus1 = self.indexInBackBucketPlus1 - 1 
            return
        }

        if self.backBucketIndexPlus1 == 1 {
            return // empty
        }
        set self.backBucketIndexPlus1 = self.backBucketIndexPlus1 - 1
        bucket = self.map.buckets[self.backBucketIndexPlus1 - 1]
        set self.indexInBackBucketPlus1 = bucket.size
    }

    export override get fn size(self) -> UWord {
        self.checkNotModified()

        return self.map.size
    }
}