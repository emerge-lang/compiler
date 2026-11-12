package emerge.platform

// The root token: it stands for the state of the process that no emerge value holds. The platform constructs the
// one instance there is and passes it to the main function of the program.
export token class World {
    private nothrow constructor {}
}
