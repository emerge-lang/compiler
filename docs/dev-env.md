# Setting up a development Environment

This being a Kotlin/JVM codebase, you need the typical tools for that:

* A JDK version 21 or newer (see [](.java-version))
* Maven 3
* maven will handle all JVM-ecosystem dependencies for you

## Dependencies

### LLVM

#### Linux host

To run the compiler on Ubuntu, install `llvm-20` and `lld-20` so that e.g. `llc-20` is available as a command.
Create a local copy of [](toolchain-config.yml.dist) and adapt it to your setup. You can then pass the path to
that file to your development build of the compiler.

#### Windows host

The windows distributions of LLVM don't include some important tools, e.g. a linker (`lld`). This project
contains [a GitHub action to compile a windows build of LLVM](.github/workflows/build-llvm-windows.yaml)
that includes the `lld` linker as a Windows executable.  You need to copy the build outputs of that action
to the Windows machine you want to run the compiler on and then point the emerge compiler to that LLVM
distribution. Say you extract the files to `F:\LLVM\20.1.8` so that e.g. `llc` is located at
`F:\LLVM\20.1.8\bin\llc.exe`. Then you need to set `backends.x86_64-pc-linux-gnu.llvm-installation-directory`
in toolchain-config.yml to `F:\LLVM\20.1.8` (copy from [](toolchain-config.yml.dist))

### Pre-Built binaries

As this project works with binaries entirely outside the JVM world, it's not possible to satisfy
all dependencies from there. You need a couple more things:

#### C-runtime startup files ("crtstuff", to quote gcc)

For all linux targets you need some binaries from GNU libc and gcc, so the emerge compiler can link them
into the linux executables. You can grab them from linux distro images compatible with the target, or [build
them yourself (see the GitHub Actions Workflow)](.github/workflows/build-emerge.yaml).
Store the binaries in you development/build environment (e.g. in `/local-resources`) and put their paths
into `toolchain-config.yml` in the project root (copy from [](toolchain-config.yml.dist))

## Building

With the dependencies available, you can use standard maven commands:

```bash
# compile and package
mvn clean package

# compile, package and run all tests
mvn clean verify
```