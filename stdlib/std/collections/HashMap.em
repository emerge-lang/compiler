package emerge.std.collections

import emerge.core.safemath.{plusModulo, minusModulo}
import emerge.core.range.{SizedRange, BidirectionalRange, EmptyRangeException}
import emerge.core.hash.{Hashable, HashAlgorithm, hashWith}

export class HashMap<Key : const Hashable & Equatable<Key>, Value> : Map<Key, Value> {
    private var buckets = Array.new::<mut ArrayList<mut MapEntry<Key, Value>>?>(16, null)
    private var hashAlgorithm: HashAlgorithm<UWord> = init
    private var maxBucketSize: UWord = 4
    private var version: UWord = 0
    private var _size: UWord = 0

    export override operator fn setAtIndex(self: mut _, index: Key, value: Value) -> Value? {
        return self.storeEntry(MapEntry(index, value), true)
    }

    private fn storeEntry(self: mut _, entry: mut MapEntry<Key, Value>, grow: Bool) -> Value? {
        hash = entry.key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(self.buckets.size - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            foreach bucketEntry in bucket {
                if isNull(bucketEntry) {
                    continue
                }

                if bucketEntry.key.equals(entry.key) {
                    previousValue = bucketEntry.value
                    self.bumpVersion()
                    set bucketEntry.value = entry.value
                    return previousValue
                }
            }

            if grow and bucket.size > self.maxBucketSize {
                self.growAndRehash()
                return self.storeEntry(entry, false)
            }
        } else {
            set bucket = ArrayList::<mut MapEntry<Key, Value>>()
            set self.buckets[bucketIndex] = bucket
        }

        self.bumpVersion()
        bucket.add(entry)
        set self._size = self._size + 1
        return null
    }

    export override operator fn getAtIndex(self, borrow index: Key) -> Value? {
        return self.getEntry(index)?.value
    }

    export override operator fn contains(self, borrow key: Key) -> Bool {
        return not isNull(self.getEntry(key))
    }

    private fn getEntry(self, borrow key: Key) -> MapEntry<Key, Value>? {
        hash = key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(self.buckets.size - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            foreach entry in bucket {
                if entry.key.equals(key) {
                    return entry
                }
            }
        }
        
        return null
    }

    export override fn remove(self: mut _, borrow key: Key) -> Value? {
        hash = key.hashWith(self.hashAlgorithm)
        bucketIndex = hash.bitwiseAnd(self.buckets.size - 1)
        var bucket = self.buckets[bucketIndex]
        if not isNull(bucket) {
            foreach entryIndex in 0..<bucket.size {
                entry = bucket[entryIndex]
                if entry.key.equals(key) {
                    bucket.removeAtIndex(entryIndex)
                    set self._size = self._size - 1
                    return entry.value
                }
            }
        }

        return null
    }

    export override fn asRange(capture self) -> HashMapRange<Key, Value> = HashMapRange(self)

    export override get fn size(self) -> UWord = self._size
    
    private fn growAndRehash(self: mut _) {
        self.bumpVersion()
        var oldBuckets = self.buckets
        set self.buckets = Array.new::<mut ArrayList<mut MapEntry<Key, Value>>?>(self.buckets.size * 2, null)
        set self._size = 0
        foreach bucket in oldBuckets  {
            if isNull(bucket) {
                continue
            }
            foreach entry in bucket {
                self.storeEntry(entry, false)
            }
        }
    }

    private fn bumpVersion(self: mut _) {
        set self.version = self.version.plusModulo(1 as UWord)
    }
}

export class HashMapRange<Key : const Hashable & Equatable<Key>, Value> : SizedRange<read MapEntry<Key, Value>> & BidirectionalRange<read MapEntry<Key, Value>> {
    private map: HashMap<Key, Value> = init
    private atVersion: UWord = self.map.version
    private var frontBucketIndex: UWord = 0
    private var indexInFrontBucket: UWord = 0
    private var backBucketIndexPlus1: UWord
    private var indexInBackBucketPlus1: UWord

    private nothrow constructor {
        set self.backBucketIndexPlus1 = self.map.buckets.size
        while self.backBucketIndexPlus1 > 0 and isNull(self.map.buckets.getOrPanic(self.backBucketIndexPlus1.minusModulo(1 as UWord))) {
            set self.backBucketIndexPlus1 = self.backBucketIndexPlus1.minusModulo(1 as UWord)
        }
        set self.indexInBackBucketPlus1 = self.map.buckets.getOrPanic(self.backBucketIndexPlus1.minusModulo(1 as UWord))?.size ?: 0
    }

    private fn checkNotModified(self) {
        if self.map.version != self.atVersion {
            throw ConcurrentModificationError()
        }
    }

    export override get fn front(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.frontBucketIndex >= self.map.buckets.size {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.frontBucketIndex]!!
        if self.indexInFrontBucket >= bucket.size {
            throw EmptyRangeException()
        }

        return bucket[self.indexInFrontBucket]
    }

    export override fn popFront(self: mut _) {
        if self.frontBucketIndex >= self.map.buckets.size {
            return
        }

        set self.indexInFrontBucket = self.indexInFrontBucket + 1

        var bucket = self.map.buckets[self.frontBucketIndex]!!
        if self.indexInFrontBucket >= bucket.size {
            set self.indexInFrontBucket = 0
            do {
                set self.frontBucketIndex = self.frontBucketIndex + 1
            } while self.frontBucketIndex < self.map.buckets.size and isNull(self.map.buckets[self.frontBucketIndex])
        }
    }

    export override get fn back(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.backBucketIndexPlus1 == 0 or self.indexInBackBucketPlus1 == 0 {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.backBucketIndexPlus1 - 1]!!
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

        while self.backBucketIndexPlus1 > 1 and isNull(self.map.buckets[self.backBucketIndexPlus1 - 1]) {
            set self.backBucketIndexPlus1 = self.backBucketIndexPlus1 - 1
        }
        bucket = self.map.buckets[self.backBucketIndexPlus1 - 1]
        set self.indexInBackBucketPlus1 = bucket?.size ?: 0
    }

    export override get fn size(self) -> UWord {
        self.checkNotModified()

        return self.map.size
    }
}