package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.common.CanonicalElementName

interface IrBaseType {
    /**
     * The supertypes of this type; **must not include emerge.core.Any!!**
     */
    val supertypes: Set<IrInterface>
    val canonicalName: CanonicalElementName.BaseType
    val parameters: List<Parameter>

    /**
     * All member functions that can be found in this type, including inherited ones. Type-check on
     * [IrFullyInheritedMemberFunction] and look at [IrMemberFunction.overrides] to distinguish.
     */
    val memberFunctions: Collection<IrOverloadGroup<IrMemberFunction>>

    interface Parameter {
        val name: String
        val bound: IrType
    }
}

interface IrIntrinsicType : IrBaseType {
    override val memberFunctions: Collection<IrOverloadGroup<IrMemberFunction>> get() = emptySet()
}

interface IrInterface : IrBaseType

interface IrClass : IrBaseType {
    /**
     * the data in this list is informative rather than functional. Possible exceptions are certain intrinsics
     * such as autoboxing and array size.
     */
    val memberVariables: List<MemberVariable>

    /**
     * Information on the actual data to be stored in instances of the class
     */
    val fields: List<Field>

    val constructor: IrFunction

    val destructor: IrFunction

    val declaredAt: IrSourceLocation

    interface MemberVariable {
        val name: String

        val type: IrType

        /**
         * how to read this member variable
         */
        val readStrategy: AccessStrategy

        /**
         * how to write this member variable
         */
        val writeStrategy: AccessStrategy

        val declaredAt: IrSourceLocation

        sealed interface AccessStrategy {
            /**
             * The member variable is supposed to be read/written by directly accessing the [Field] with [Field.id] == [BareField.fieldId].
             */
            interface BareField : AccessStrategy {
                val fieldId: Int
            }

            // once custom getters and setters are a thing, they'll be added here
        }
    }

    interface Field {
        /**
         * an [Int] value unique among all [Field]s of one [IrClass]. The purpose is to identify this field by something
         * else other than the JVM object identity.
         */
        val id: Int

        val type: IrType
    }
}