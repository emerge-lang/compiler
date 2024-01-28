# The "Platform" abstraction

The combination of hardware and OS is called the "platform". Emerge as a language (that is: syntax,
semantics and standard library) should be independent from the platform it runs on. Practical limitations
will certainly limit the variety of platforms that are supported, but it should be able to add more without
touching the language core.
Any compilation process always targets a single platform

Thus,
* The standard library may not interact with any platform-specific API. Memory allocation is a slight exception,
  but that is abstracted away by the compiler so while the stdlib does technically interact with the OS here,
  the exact way of doing it is not baked into the language or the stdlib implementation.
* All platform implementation details are inside the `emerge.platform` module, which is always supplied by the
  compiler backend as per the target platform. The stdlib can import from `emerge.platform` to implement
  OS or hardware specific functionality. `emerge.platform` should focus on providing as small primitives as possible
  so that the standard library sources remain descriptive and informative. This should also make it far easier to
  add new targets, as the implementation scope is smaller