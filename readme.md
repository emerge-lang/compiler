# Emerge Lang (Toy language, working title)

I am building a toy language here with the main goal of entertaining myself.
You're invited to talk, exchange ideas, contribute, ... in case it entertains you, too.

## Dependencies for running the compiler

### LLVM

#### Linux host

To run the compiler on linux, install `llvm-18` so that e.g. `llc-18` is available as a command.

#### Windows host

The windows distributions of LLVM don't include some important tools, e.g. a linker (`lld`). This project
contains [a GitHub action to compile a windows build of LLVM](.github/workflows/build-llvm-windows.yaml)
that includes the `lld` linker as a Windows executable.  You need to copy the build outputs of that action
to the Windows machine you want to run the compiler on and then point the emerge compiler to that LLVM
distribution. Say you extract the files to `F:\LLVM\18.1.5` so that e.g. `llc` is located at
`F:\LLVM\18.1.5\bin\llc.exe`. Then you need to set the Java system property `emerge.backend.llvm.llvm-18-dir`
to `F:\LLVM\18.1.5`:

    -Demerge.backend.llvm.llvm-18-dir=F:\LLVM\18.1.5

## Development

This being a Kotlin/JVM codebase, you need the typical tools for that:

* A JDK version 21 or newer (see [](.java-version))
* Maven 3
* maven will handle all JVM-ecosystem dependencies for you

### Dependencies

As this project works with binaries entirely outside the JVM world, its not possible to satisfy
all dependencies from there. You need a couple more things:

#### C-runtime startup files ("crtstuff", to quote gcc)

For all linux targets you need some binaries from GNU libc and gcc, so the emerge compiler can link them
into the linux executables. You can grab them from linux distro images compatible with the target, or [build
them yourself (see the GitHub Actions Workflow)](.github/workflows/build-emerge.yaml).
Store the binaries in you development/build environment (e.g. in `/local-resources`) and put their paths
into `external-deps.properties` in the project root (copy from [](external-deps.properties.dist))

### Building

With the dependencies available, you can use standard maven commands:

```bash
# compile and package
mvn clean package

# compile, package and run all tests
mvn clean verify
```
