package emerge.platform

import emerge.std.io.PrintStream

export fn putDemangledNameTo(mangledName: String, borrow stream: mut PrintStream) {
    if not mangledName.startsWith("$EM") {
        stream.put(mangledName)
        return
    }
    
    
}