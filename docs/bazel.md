# Building emerge programs with Bazel

This page describes how to set up a build using the [bazel build tool](https://bazel.build) to build a
program written in emerge.

*Bazel is a beast in-and-of itself. If you want to understand all that is going on, prepare to dig through the
bazel documentation and sources quite a bunch. However, setting up a project by copy-🍝ing from this page is simple.*

## Getting Started

### 1. Install necessary software

1. install the latest version of the emerge toolchain, see [the main readme](../readme.md).
2. install bazelisk, a version management for bazel: https://github.com/bazelbuild/bazelisk

### 2. Determine your project name, location, ...

1. If you don't have one already, create some space for your emerge program to live in. For this tutorial,
   say we store our project in `~/coding/emerge-demo`. So:

   ```bash
   mkdir -p ~/coding/emerge-demo && pushd $_
   ```
2. choose an emerge package name for your project. Like in the JVM world, this should be your reverse domain name.
   So this could be e.g. `com.acme.frobnicator` or `io.github.myusername.fiddleproject`

### 3. Configure Bazel

1. Add a new file `.bazelrc` with the following content:
   ```
   common --registry=https://raw.githubusercontent.com/emerge-lang/bazel-registry/tree/main
   common --registry=https://bcr.bazel.build
   ```
2. Add a new file `MODULE.bazel` with the following content:
    ```python
    bazel_dep(
        name = "rules_emerge",
        version = "0.1.0",       # !!! replace with the latest version of emerge
    )
    ```
3. Add a new file `BUILD` with the following content:
   ```
   # this tells bazel that there is one emerge module in your project
   emerge_module(
       name = "com.acme.frobnicator",     # !!! replace with your emerge package name
       source_director = "src"            # this is where your source files will live, relative to the BUILD file
   )
   
   # this tells bazel to compile your emerge module to an executable
   emerge_binary(
       name = "my_binary",                         # this name is only relevant for invoking bazel
       root_module = ["//:com.acme.frobnicator"],  # this tells bazel that your executable should contain the com.acme.frobnicator module
   )
   ```
4. Create the source directory and add some code
   ```bash
   mkdir src
   ```

Your project directory should now look like so:

```
~/coding/emerge-demo
├── .bazelrc
├── BUILD
├── MODULE.bazel
└── src
```
   
### 4. Write some code

You can now add code in the `src/` directory. Like in Java, the directory sturcture of your source tree must
match the package structure in the emerge semantics. However, the common prefix for your project (`com.acme.frobnicator`
in the example) can be omitted. So, e.g., create `src/main.em` with this content:

```
package com.acme.frobnicator

import emerge.platform.StandardOut

mut fn main() {
    StandardOut.put("Hello, World!")
}
```

### 5. Compile and run your program

You can now build your program by running

```bash
bazelisk build //:my_binary
```

It should output something like this:

```
INFO: Analyzed target //:my_binary (84 packages loaded, 385 targets configured).
INFO: From Compiling binary bazel-out/k8-fastbuild/bin/x86_64-pc-linux-gnu/runnable; 1 emerge module: ["com.acme.frobnicator"]:
----------
lexical analysis: 587.087ms
semantic analysis: 302.676ms
backend: 2.204s
total time: 3.111s
INFO: Found 1 target...
Target //:my_binary up-to-date:
  bazel-bin/x86_64-pc-linux-gnu/runnable
INFO: Elapsed time: 5.532s, Critical Path: 4.97s
INFO: 3 processes: 2 internal, 1 linux-sandbox.
INFO: Build completed successfully, 3 total actions
````

_If you get an error about a missing toolchian, you either didn't install the emerge toolchain properly or you are
running the build on a platform other than Linux on an x86_64 CPU. In the latter case, see [Cross-Compilation](#Cross-compilation)._

You can see that bazel has put your compiled program at `bazel-bin/x86_64-pc-linux-gnu/runnable`. So now we can run it,
and it should print "Hello, World!":

```bash
bazel-bin/x86_64-pc-linux-gnu/runnable
```

## Multiple emerge modules

If you want to split your program into multiple emerge modules, this is easily done in the bazel build. Say we want
to split out a `com.acme.frobnication` module from our program to separate logic from UI. Start by declaring a second
`emerge_module` in `BUILD`:

```python
emerge_module(
    name = "com.acme.frobnication",
    source_directory = "lib",
)
```

Then, declare a dependency from your main program to your library module:

```python
emerge_module(
    name = "com.acme.frobnicator",
    source_directory = "src",
    uses = ["//:com.acme.frobnication"],
)
```

You can now refactor your code to move the core logic into the `lib` subdirectory and keep IO/UI related code in
`src`.

## Cross-compilation

Right now, the emerge compiler only supports compiling for `x86_64` on `linux`, so it's not like you have much
of a choice.  But if you try to run the build e.g. on ARM, bazel will try to build your program for ARM by default. That's just
how bazel works. To tell bazel to compile for x86_64+linux:

1. declare a platform in your `BUILD` file
   ```python
   platform(
       name = "linux_x64",
       constraint_values = [
           "@platforms//os:linux",
           "@platforms//cpu:x86_64",
       ]
   )
   ```
2. invoke bazel with `--platforms=//:linux_x64`:
   ```bash
   bazelisk build //:my_binary --platforms=//:linux_x64
   ```

See also: https://bazel.build/concepts/platforms

## Accessing the C FFI

To access the C FFI, you need to declare a dependency on the `emerge.ffi.c` module; otherwise, the emerge compiler
will not allow you to access the C FFI specific data-types and functions:

```
(ERROR) Module com.acme.frobnicator cannot access class CPointer because it doesn't declare a dependency on module emerge.ffi.c. Declare that dependency (this should be done by your build tool, really).

in .../src/main.em:
  |
7 |      println("Hello, World!")
8 |      x: CPointer<S32>? = null
  |     ☝️
9 |  }
  |
```

`emerge.ffi.c` is a module supplied by the toolchain, not by the library ecosystem. To refer to these "built-in" modules,
use the `@rules_emerge//builtin_module` bazel-package. In your `BUILD` file:

```python
emerge_module(
    name = "com.acme.frobnication",
    source_directory = "lib",
    uses = [
        "@rules_emerge//builtin_module:emerge.ffi.c",
    ],
)
```