package compiler.compiler

val SHOULD_WRITE_GOLDEN_FILES: Boolean by lazy {
    System.getenv("GOLDEN_FILE_TESTS_WRITE") == "true"
}