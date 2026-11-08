package compiler.compiler.binding

import compiler.compiler.negative.moduleBackendIrAssumingNoErrors
import compiler.compiler.negative.validateModule
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDropStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrModule
import io.github.tmarsteel.emerge.backend.api.ir.IrReifiedTypeExpression
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
import io.kotest.matchers.collections.shouldContain
import io.kotest.matchers.collections.shouldHaveSize
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class ReificationIrTests : FreeSpec({
    val module: IrModule = validateModule("""
        fn f<T>(x: T) {}
        fn g<T>(x: T?) {}
        class C<T> {
            x: T = init
            fn m<U>(self, u: U) {}
        }
    """.trimIndent()).moduleBackendIrAssumingNoErrors()
    val pkg = module.packages.single()
    val classC = pkg.classes.single { it.canonicalName.simpleName == "C" }

    "a plain reference to a type parameter keeps the nullability of the type argument, `T?` overrides it" {
        val f = pkg.functions.single { it.canonicalName.simpleName == "f" }.overloads.single()
        f.parameters.single().type.shouldBeInstanceOf<IrGenericTypeReference>().nullabilityOverride shouldBe null

        val g = pkg.functions.single { it.canonicalName.simpleName == "g" }.overloads.single()
        g.parameters.single().type.shouldBeInstanceOf<IrGenericTypeReference>().nullabilityOverride shouldBe true
    }

    "functions receive their declared type parameters" {
        val f = pkg.functions.single { it.canonicalName.simpleName == "f" }.overloads.single()
        f.typeParameters.map { it.name } shouldBe listOf("T")

        val m = classC.memberFunctions.single { it.canonicalName.simpleName == "m" }.overloads.single()
        m.typeParameters.map { it.name } shouldBe listOf("U")
    }

    "constructors receive the class type parameters, destructors none" {
        classC.constructor.typeParameters.map { it.name } shouldBe listOf("T")
        classC.destructor.typeParameters.shouldBeEmpty()
    }

    "classes store their type parameters in hidden fields" {
        classC.fields shouldHaveSize 2
        val (parameter, field) = classC.typeParameterFields.entries.single()
        parameter.name shouldBe "T"
        parameter shouldBe classC.parameters.single()
        classC.fields shouldContain field

        val assignment = classC.constructor.body!!.flatten()
            .filterIsInstance<IrAssignmentStatement>()
            .single { (it.target as? IrAssignmentStatement.Target.ClassField)?.field == field }
        val assignedValue = assignment.value.declaration.value.shouldBeInstanceOf<IrReifiedTypeExpression>()
        assignedValue.type.shouldBeInstanceOf<IrGenericTypeReference>().parameter shouldBe parameter

        val droppedFields = classC.destructor.body!!.flatten()
            .filterIsInstance<IrDropStrongReferenceStatement>()
            .mapNotNull { (it.reference.declaration.value as? IrClassFieldAccessExpression)?.field }
            .toList()
        droppedFields shouldContain field
    }
})

private fun IrExecutable.flatten(): Sequence<IrExecutable> = sequence {
    yield(this@flatten)
    if (this@flatten is IrCodeChunk) {
        components.forEach { yieldAll(it.flatten()) }
    }
}
