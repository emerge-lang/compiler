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
                    self.bumpVersion()
                    return entry.value
                }
            }
        }

        return null
    }

    export override fn asRange(capture self) -> own HashMapRange<Key, Value> = HashMapRange(self)

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

    // @return the number of entries in the bucket at [index]; 0 if there is no such bucket
    private nothrow fn bucketSizeOrZero(self, index: UWord) -> UWord {
        if index >= self.buckets.size {
            return 0
        }

        return self.buckets.getOrPanic(index)?.size ?: 0
    }

    // @return the index of the first bucket at or after [index] that has entries; buckets.size if there is none
    private nothrow fn nextNonEmptyBucket(self, index: UWord) -> UWord {
        var candidate = index
        while candidate < self.buckets.size {
            if self.bucketSizeOrZero(candidate) > 0 {
                return candidate
            }
            set candidate = candidate.plusModulo(1 as UWord)
        }

        return self.buckets.size
    }

    // @return 1 + the index of the last bucket before [indexPlus1] that has entries; 0 if there is none
    private nothrow fn previousNonEmptyBucketPlus1(self, indexPlus1: UWord) -> UWord {
        var candidatePlus1 = indexPlus1
        while candidatePlus1 > 0 {
            if self.bucketSizeOrZero(candidatePlus1.minusModulo(1 as UWord)) > 0 {
                return candidatePlus1
            }
            set candidatePlus1 = candidatePlus1.minusModulo(1 as UWord)
        }

        return 0
    }
}

export class HashMapRange<Key : const Hashable & Equatable<Key>, Value> : SizedRange<read MapEntry<Key, Value>> & BidirectionalRange<read MapEntry<Key, Value>> {
    private map: HashMap<Key, Value> = init
    private atVersion: UWord = self.map.version
    private var remaining: UWord = self.map._size
    private var frontBucketIndex: UWord = 0
    private var indexInFrontBucket: UWord = 0
    private var backBucketIndexPlus1: UWord = 0
    private var indexInBackBucketPlus1: UWord = 0

    private nothrow constructor {
        set self.frontBucketIndex = self.map.nextNonEmptyBucket(0)
        set self.backBucketIndexPlus1 = self.map.previousNonEmptyBucketPlus1(self.map.buckets.size)
        set self.indexInBackBucketPlus1 = self.map.bucketSizeOrZero(self.backBucketIndexPlus1.minusModulo(1 as UWord))
    }

    private fn checkNotModified(self) {
        if self.map.version != self.atVersion {
            throw ConcurrentModificationError()
        }
    }

    export override get fn front(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.remaining == 0 {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.frontBucketIndex]!!
        return bucket[self.indexInFrontBucket]
    }

    export override fn popFront(self: mut _) {
        self.checkNotModified()

        if self.remaining == 0 {
            return
        }

        set self.remaining = self.remaining - 1
        set self.indexInFrontBucket = self.indexInFrontBucket + 1
        if self.indexInFrontBucket >= self.map.bucketSizeOrZero(self.frontBucketIndex) {
            set self.frontBucketIndex = self.map.nextNonEmptyBucket(self.frontBucketIndex + 1)
            set self.indexInFrontBucket = 0
        }
    }

    export override get fn back(self) -> read MapEntry<Key, Value> {
        self.checkNotModified()

        if self.remaining == 0 {
            throw EmptyRangeException()
        }

        bucket = self.map.buckets[self.backBucketIndexPlus1 - 1]!!
        return bucket[self.indexInBackBucketPlus1 - 1]
    }

    export override fn popBack(self: mut _) {
        self.checkNotModified()

        if self.remaining == 0 {
            return
        }

        set self.remaining = self.remaining - 1
        if self.indexInBackBucketPlus1 > 1 {
            set self.indexInBackBucketPlus1 = self.indexInBackBucketPlus1 - 1
            return
        }

        set self.backBucketIndexPlus1 = self.map.previousNonEmptyBucketPlus1(self.backBucketIndexPlus1 - 1)
        set self.indexInBackBucketPlus1 = self.map.bucketSizeOrZero(self.backBucketIndexPlus1.minusModulo(1 as UWord))
    }

    export override get fn size(self) -> UWord {
        self.checkNotModified()

        return self.remaining
    }
}