package emerge.core

/// Marks types that can be annotations or can be stored in an annotation. The compiler will verify that only classes
/// have this annotation and that all members of annotated classes are core scalars. To be extended in the future:
/// * so that annotations can be cycle-free object trees.
/// * with a targeting directive like in Java, so the "only on classes" rule can be encoded in here instead of being
///   in the compiler, e.g. #[Annotatable(targets = [ClassAnnotationTarget])]
#[Annotatable()]
export class Annotatable {
}