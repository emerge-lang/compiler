# Inheritance in Emerge

Emerge supports OOP style objects, interfaces and classes. Multiple inheritance is limited.

The following constraints are placed on emerge programs:

* objects can only be created from a pre-defined `class`
* one class can inherit from (= implement) n `interface`s
* classes can not inherit from/extend other classes
* interfaces can inherit from n other interfaces
* the graph of inheritance must be a tree/acyclic.
* interfaces cannot declare implementations for member functions
  (this is currently possible, but will be removed as soon as mixins are stable)

## Mixins

To facilitate code-reuse, classes can mix-in other objects/classes. When `class A` mixes in an
instance of `interface B`, all calls to the member functions of `interface B` will be delegated to
the mixed-in object. The class can override any member function from `interface B`.

The important difference between mixin-based delegation and traditional multiple inheritance is the
value of the `self` pointer in mixed-in functions. It points to the mixed-in object, not to the object
that defines the mixin. This simplifies mixins from a complex semantic construct to pure syntax sugar.
If the behavior of a mixed-in function should vary per host object, this variance needs to be explicitly
passed to the mixed-in object e.g. as a lambda function. This way, the multiple-inheritance "magic" is
forced to be visible.

Given
```
interface I {
  fn foo(self)
}
class Mixin : I {
  fn foo(self)
}
```

Then this:
```
class Concrete : I {
  constructor {
    mixin Mixin()
  }
}
```

is syntax-sugar for

```
class Concrete : I {
  private _mixin = Mixin()
  override fn foo(self) = self._mixin.foo() 
}
```

## Determining the concrete member function implementations for a class

This section describes the algorithm by which the concrete member function implementations are chosen
for a class (=concrete type).

### Layer 1: Inherited member functions

The set of member functions that an `interface I` defines is those inherited from its supertypes, plus
those declared in the interface declaration. An interface can `override` functions from a parent interface
to refine the signature of certain functions. LSP applies, of course.

The set of inherited member functions for a `class A` is the set of member functions defined or inherited from all its
supertypes. Member functions are unique by their signature only. Diamond problems have to be resolved by the
programmer in the declaration of `class A`.

The inherited member functions form Layer 1 of the concrete implementation selection.

TODO: how to resolve diamond problems in interface-only hierarchies?

### Layer 2: mixed-in functions

For every mixin declaration, the mixed-in object will "consume" all the supertypes of which it is a subtype. Consume
means that this mixed-in object will receive delegated calls. If two mixins are declared that have a non-empty conjunction
type, the mixin that was declared first will consume the conjunction type:

```
interface I1 {
    fn foo(self)
}
interface I2 {
    fn bar(self)
}
interface I3 {
    fn blah(self)
}

class M1 : I1 | I2 {
    fn foo(self) {}
    fn bar(self) {}
}

class M2 : I2 | I3 {
    fn bar(self) {}
    fn blah(self) {}
}

class Concrete : I1 | I2 | I3 {
    constructor {
        mixin M1() // calls to foo() and bar() will be delegated to M1
        mixin M2() // M1 has consumed I1 and I2, so M2 will only take responsibility for I3
                   // hence, only calls to blah() will be delegated to M2
    }
}
```

### Layer 3: overriding functions

Methods in the concrete type/class that `override` inherited functions will take precedence over mixed-in
implementations.

### Layer 4: class-specific/declared functions

Member functions declared on the class that do not override are used as-is. There is no effective difference
between these and a top-level function with UFCS. They do not appear in the v-table because calling them always
requires a reference of a concrete, final type; and such calls always use static dispatch.

### Example

Putting abstract methods on the X axis and the layers on the Y axis in reverse order,
you can determine the selected concrete implementation by finding the first non-empty
layer cell from the bottom upwards. 

| Layer      | Method 1 | Method 2 | Method 3 | Method 4 | Method 5                           |
|------------|----------|----------|----------|----------|------------------------------------|
| supertypes | inherit  | inherit  | inherit  | -        | inherit                            |
| mixin 2    | mixin    | mixin    | mixin    | -        | -                                  |
| mixin 1    | -        | mixin    | -        | -        | -                                  |
| override   | override | -        | -        | -        | -                                  |
| declare    | -        | -        | -        | declare  | -                                  |
| **result** | override | mixin 1  | mixin 2  | declare  | error: abstract fn not implemented |