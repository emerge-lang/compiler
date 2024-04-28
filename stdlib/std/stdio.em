package emerge.std

import emerge.platform.print

export mutable fun println(str: String) {
    print(str)
    print("\n")
}