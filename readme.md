# Emerge Lang

Emerge wants to be a programming language that gets out of your way, so you can freely experiment with your
thoughts and challenges, until the solution _emerges_ eventually.  

```
// obligatory Hello World in emerge
 
package compilerdemo

import emerge.platform.StandardOut

mut fn main() {
   StandardOut.put("Hello, World!\n")
}
```

Key features:

* mutability is a core part of the type system (like D)
* automatic memory management (reference counting, no GC)
* enables both functional and OOP style code; as well as combining the two
* actor-style concurrency 
* statically typed, with lots of type-inference to keep your code clean and eloquent
* compiled ahead of time to native machine code using LLVM

This is **a toy language** with the main purpose of entertainment and education.
Feedback, ideas, discussions, exchanges, ... is all very welcome 🙂

## Installation

### Debian-based linux

Download the latest `.deb` package from the [releases page][1].
Install using

```bash
sudo apt install -f ~/Downloads/emerge-toolchain-{INSERT VERSION}.deb
```

### Other linux distros

Install the dependencies manually:

* `llvm-18`
* `lld-18`
* a Java runtime >= 21

Download the latest `.tar.gz` package from the [releases page][1]. Then run **after filling in**:

```sh
VERSION="<INSERT VERSION, e.g. 1.4.2>"
sudo mkdir -p "/opt/emerge-toolchain/$VERSION"
sudo tar -xp --directory=/opt/emerge-toolchain/$VERSION -f "emerge-toolchain-$VERSION.tar.gz" 
sudo /opt/emerge-toolchain/$VERSION/configure.sh
```

### Windows

Nothing to do 🎉; the build tool bazel will handle downloading and managing compiler installations for you.

### Updating

Upgrading works the same way. Each compiler release gets its own package, so you can run multiple versions
in parallel (reproducible builds ❤️).

## Running the compiler

The officially supported build tool for emerge is [bazel](https://bazel.build). See [docs/bazel.md](docs/bazel.md)
for how to set up a bazel-build for emerge (it's really simple).

[1]: https://github.com/emerge-lang/compiler/releases