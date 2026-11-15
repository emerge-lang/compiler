# Integration tests

Each directory in [programs](programs) is an emerge program. `ProgramTests` compiles every one of them with the
built toolchain, the way a user would (`java -jar toolchain.jar ... compile`) and for `x86_64-pc-linux-gnu`, runs the
binary and compares what it does with what is written down next to the sources.

The unit tests of the frontend cover what the compiler rejects. These tests cover that what it accepts does the right
thing when it runs.

## Adding a program

```
programs/
  myprogram/                the module is named like the directory
    src/                    all sources; their package is myprogram, or a package below it
      main.em
    expected-stdout.txt     required: the exact standard output
    expected-exit-code.txt  optional, defaults to 0
```

The standard error output is not compared, as stack traces contain addresses. It is shown when a test fails.

Keep the output deterministic, and print a line for everything worth checking: a program that crashes or misbehaves
should not be able to produce the expected output by accident.

## Running them

The tests run in the `integration-test` phase of maven, not in `test`: what they test is the runnable jar, which only
exists once the toolchain module is packaged.

### Against the toolchain built in the working copy

```
mvn -pl toolchain -am package -DskipTests
mvn -pl integration-tests verify
```

This uses `toolchain/target/toolchain.jar` and the `toolchain-config.yml` in the root of the repository. Create that
file from `toolchain-config.yml.dist`; it is not in git, as it says where LLVM and the C runtime files are on your
machine. Mind that the second command does not rebuild the toolchain.

### Against an installed toolchain

```
mvn -pl integration-tests verify -Demerge.integration-tests.toolchain-dir=<directory>
```

The directory is laid out like the distributable archives: `bin/toolchain.jar`, `toolchain-config.yml`, and
optionally a `jre`. Without a `jre`, the JVM that runs the tests also runs the toolchain.

### Requirements

Running a linux binary must be possible: either the tests run on x86_64 linux, or on windows with a working
`wsl.exe`.

When the toolchain or a way to run the binaries is missing, the tests fail and say what is missing. With
`-Demerge.integration-tests.optional=true` the programs are skipped instead, and the reason is printed.

What the compiler wrote, along with the project configuration generated for it, is kept in `target/programs/<name>`.
