package emerge.std

import emerge.platform.print

export mut fn println(str: String) {
    print(str)
    print("\n")
}