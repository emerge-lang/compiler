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

There currently is no easy way to install into windows natively. Use WSL or go through the steps below
to set up a development environment for the compiler.

### Updating

Upgrading works the same way. Each compiler release gets its own package, so you can run multiple versions
in parallel (reproducible builds ❤️).

## Running the compiler

*Note: An integration with [bazel](https://bazel.build) is in the works, and it will be the official way to run
the compiler. Until then, or if you want to hack around:*

After you have the toolchain installed, you need to collect the constituents of the compiler invocation
1. the JRE executable. After installation, there is a convenient symlink in the directory of the toolchain,
   so you can confidently hard-code the JRE executable to be this: 
   `/opt/emerge-toolchain/$VERSION/jre/bin/java`
2. the `toolchain-config.yml` that tells the compiler where its static resources are. This is also installed
   and set up automatically, so you can also hardcode this one:
   `/opt/emerge-toolchain/$VERSION/toolchain-config.yml`
3. **A `project-config.yml` for the codebase you want to compile.** This tells the compiler all it needs to know
   about the specific build it has to carry out. An example:
   ```yaml
   modules:
     - name: compilertest
       sources: ./src
       uses:
         - emerge.ffi.c
   targets:
     x86_64-pc-linux-gnu:
       output-directory: ../emerge-out
   ```
   This tells the compiler that:
    * your project consists of one emerge module, called `compilertest`
        * with its sources located at `./src` (paths are always relative to the yml file)
        * this module depends on the `emerge.ffi.c` module, enabling your code to use the C FFI
    * you want to build the `x86_64-pc-linux-gnu` target. The output should be put into `../emerge-out`

## Development Environment

This being a Kotlin/JVM codebase, you need the typical tools for that:

* A JDK version 21 or newer (see [](.java-version))
* Maven 3
* maven will handle all JVM-ecosystem dependencies for you

### Dependencies

#### LLVM

##### Linux host

To run the compiler on Ubuntu, install `llvm-18` and `lld-18` so that e.g. `llc-18` is available as a command.
Create a local copy of [](toolchain-config.yml.dist) and adapt it to your setup. You can then pass the path to
that file to your development build of the compiler.

##### Windows host

The windows distributions of LLVM don't include some important tools, e.g. a linker (`lld`). This project
contains [a GitHub action to compile a windows build of LLVM](.github/workflows/build-llvm-windows.yaml)
that includes the `lld` linker as a Windows executable.  You need to copy the build outputs of that action
to the Windows machine you want to run the compiler on and then point the emerge compiler to that LLVM
distribution. Say you extract the files to `F:\LLVM\18.1.5` so that e.g. `llc` is located at
`F:\LLVM\18.1.5\bin\llc.exe`. Then you need to set `backends.x86_64-pc-linux-gnu.llvm-installation-directory`
in toolchain-config.yml to `F:\LLVM\18.1.5` (copy from [](toolchain-config.yml.dist))

#### Pre-Built binaries

As this project works with binaries entirely outside the JVM world, its not possible to satisfy
all dependencies from there. You need a couple more things:

##### C-runtime startup files ("crtstuff", to quote gcc)

For all linux targets you need some binaries from GNU libc and gcc, so the emerge compiler can link them
into the linux executables. You can grab them from linux distro images compatible with the target, or [build
them yourself (see the GitHub Actions Workflow)](.github/workflows/build-emerge.yaml).
Store the binaries in you development/build environment (e.g. in `/local-resources`) and put their paths
into `toolchain-config.yml` in the project root (copy from [](toolchain-config.yml.dist))

### Building

With the dependencies available, you can use standard maven commands:

```bash
# compile and package
mvn clean package

# compile, package and run all tests
mvn clean verify
```

[1]: https://github.com/emerge-lang/compiler/releases