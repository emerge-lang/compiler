package emerge.std

import emerge.platform.print

export fun println(str: String) {
    print(str)
    print("\n")
}