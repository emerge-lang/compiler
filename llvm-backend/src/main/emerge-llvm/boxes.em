package emerge.llvm

struct ByteBox {
    value: Byte
}

fun getBoxedByte(self: readonly Array<Byte>, index: uword) -> Any {
    return ByteBox(self.get(index))
}

fun setBoxedByte(self: mutable Array<Byte>, index: uword, box: ByteBox) {
    self.set(box.value)
}

