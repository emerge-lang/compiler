/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.compiler.ast.type

import compiler.ast.type.TypeMutability
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.binding.type.beAssignableTo
import compiler.compiler.binding.type.parseType
import compiler.compiler.negative.useValidModule
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeSingleton
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.shouldNot
import io.kotest.matchers.types.shouldBeInstanceOf

class ResolvedTypeReferenceTest : FreeSpec() { init {
    "Given a type hierarchy A; B : A; C : A" - {
        val swCtx = useValidModule("""
            interface A {}
            interface B : A {}
            interface C : A {}
        """.trimIndent())

        val mutableA = swCtx.parseType("mut A")
        val readonlyA = mutableA.withMutability(TypeMutability.READONLY)
        val immutableA = readonlyA.withMutability(TypeMutability.IMMUTABLE)
        val exclusiveA = readonlyA.withMutability(TypeMutability.EXCLUSIVE)

        val mutableB = swCtx.parseType("mut B")
        val readonlyB = mutableB.withMutability(TypeMutability.READONLY)
        val immutableB = readonlyB.withMutability(TypeMutability.IMMUTABLE)

        val mutableC = swCtx.parseType("mut C")
        val readonlyC = mutableC.withMutability(TypeMutability.READONLY)
        val immutableC = readonlyC.withMutability(TypeMutability.IMMUTABLE)

        val readonlyNothing = swCtx.parseType("read Nothing")
        val mutableNothing = swCtx.parseType("mut Nothing")
        val immutableNothing = swCtx.parseType("const Nothing")

        "the closest common ancestor of" - {
            "mut B and mut A is mut A" {
                mutableA.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableA) shouldBe mutableA
            }

            "mut B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "mut B and const A is read A" {
                immutableA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "read B and mut A is read A" {
                mutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "read B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "read B and const A is read A" {
                immutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "const B and mut A is read A" {
                mutableA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "const B and read A is read A" {
                readonlyA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "const B and const A is const A" {
                immutableA.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableA) shouldBe immutableA
            }

            //----

            "mut B and mut C is mut A" {
                mutableC.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableC) shouldBe mutableA
            }

            "mut B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "mut B and const C is read A" {
                immutableC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "read B and mut C is read A" {
                mutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "read B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "read B and const C is read A" {
                immutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "const B and mut C is read A" {
                mutableC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "const B and read C is read A" {
                readonlyC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "const B and const C is const A" {
                immutableC.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableC) shouldBe immutableA
            }
            
            // ----
            "mut A and read Nothing is read A" {
                mutableA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "mut A and mut Nothing is mut A" {
                mutableA.closestCommonSupertypeWith(mutableNothing) shouldBe mutableA
                mutableNothing.closestCommonSupertypeWith(mutableA) shouldBe mutableA
            }

            "const A and read Nothing is read A" {
                immutableA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "const A and const Nothing is const A" {
                immutableA.closestCommonSupertypeWith(immutableNothing) shouldBe immutableA
                immutableNothing.closestCommonSupertypeWith(immutableA) shouldBe immutableA
            }

            "exclusive A and read Nothing is read A" {
                exclusiveA.closestCommonSupertypeWith(readonlyNothing) shouldBe readonlyA
                readonlyNothing.closestCommonSupertypeWith(exclusiveA) shouldBe readonlyA
            }
        }
    }

    "parametric supertypes" - {
        "determining type parameters for parametric supertypes" - {
            "single level of inheritance" - {
                "derived type has no parameters" {
                    val swCtx = useValidModule("""
                        interface S<T> {}
                        class D : S<U32> {}
                    """.trimIndent())

                    val baseTypeS = swCtx.parseType("S").baseTypeOfLowerBound
                    val baseTypeD = swCtx.parseType("D").baseTypeOfLowerBound
                    baseTypeD.superTypes.getParameterizedSupertype(baseTypeS) shouldBe swCtx.parseType("S<U32>")
                }

                "derived type has an unrelated parameter" {
                    val swCtx = useValidModule("""
                        interface S<T> {}
                        class D<E> : S<U32> {}
                    """.trimIndent())

                    val baseTypeS = swCtx.parseType("S").baseTypeOfLowerBound
                    val baseTypeD = swCtx.parseType("D").baseTypeOfLowerBound
                    baseTypeD.superTypes.getParameterizedSupertype(baseTypeS) shouldBe swCtx.parseType("S<U32>")
                }

                "derived type forwards parameter plainly" {
                    val swCtx = useValidModule("""
                        interface S<T> {}
                        class D<T> : S<T> {}
                    """.trimIndent())

                    val baseTypeS = swCtx.parseType("S").baseTypeOfLowerBound
                    val baseTypeD = swCtx.parseType("D").baseTypeOfLowerBound
                    val translated = baseTypeD.superTypes.getParameterizedSupertype(baseTypeS)
                    translated.inherentTypeBindings.bindings.shouldBeSingleton().single().let { (param, binding) ->
                        param shouldBe baseTypeS.typeParameters!!.single()
                        binding.shouldBeInstanceOf<BoundTypeArgument>()
                            .type.shouldBeInstanceOf<GenericTypeReference>()
                            .parameter shouldBe baseTypeD.typeParameters!!.single()
                    }
                }

                "derived type forwards parameter transformed" {
                    val swCtx = useValidModule("""
                        interface S<T> {}
                        class D<T> : S<Array<T>> {}
                    """.trimIndent())

                    val baseTypeS = swCtx.parseType("S").baseTypeOfLowerBound
                    val baseTypeD = swCtx.parseType("D").baseTypeOfLowerBound
                    val translated = baseTypeD.superTypes.getParameterizedSupertype(baseTypeS)
                    translated.inherentTypeBindings.bindings.shouldBeSingleton().single().let { (param, binding) ->
                        param shouldBe baseTypeS.typeParameters!!.single()
                        binding.shouldBeInstanceOf<BoundTypeArgument>()
                            .type.shouldBeInstanceOf<RootResolvedTypeReference>()
                            .also { it.baseType shouldBe swCtx.array }
                            .arguments.shouldNotBeNull().shouldBeSingleton().single()
                            .type.shouldBeInstanceOf<GenericTypeReference>()
                            .parameter shouldBe baseTypeD.typeParameters!!.single()
                    }
                }
            }

            "deeper inheritance" - {
                "derived type forwards parameter plainly" {
                    val swCtx = useValidModule("""
                        interface A<X> {}
                        interface B<Y> : A<Y> {}
                        class D<Z> : B<Z> {}
                    """.trimIndent())

                    val baseTypeA = swCtx.parseType("A").baseTypeOfLowerBound
                    val baseTypeD = swCtx.parseType("D").baseTypeOfLowerBound
                    val translated = baseTypeD.superTypes.getParameterizedSupertype(baseTypeA)
                    translated.inherentTypeBindings.bindings.shouldBeSingleton().single().let { (param, binding) ->
                        param shouldBe baseTypeA.typeParameters!!.single()
                        binding.shouldBeInstanceOf<BoundTypeArgument>()
                            .type.shouldBeInstanceOf<GenericTypeReference>()
                            .parameter shouldBe baseTypeD.typeParameters!!.single()
                    }
                }
            }
        }

        "closestCommonSupertypeWith" - {
            val swCtx = useValidModule("""
                interface S<T> {}
                interface A<X> : S<X> {}
                interface B<Y> : S<Y> {}
            """.trimIndent())

            "A<S32> closestCommonSupertypeWith B<S32> is S<S32>" {
                swCtx.parseType("A<S32>").closestCommonSupertypeWith(swCtx.parseType("B<S32>")) shouldBe swCtx.parseType("S<S32>")
            }

            "A<Any> closestCommonSupertypeWith B<S32> is S<out Any>" {
                swCtx.parseType("A<Any>").closestCommonSupertypeWith(swCtx.parseType("B<S32>")) shouldBe swCtx.parseType("S<out Any>")
            }

            "A<S32> closestCommonSupertypeWith B<U32> is S<out const Printable>" {
                swCtx.parseType("A<S32>").closestCommonSupertypeWith(swCtx.parseType("B<U32>")) shouldBe swCtx.parseType("S<out const Printable>")
            }

            "A<in Any> closestCommonSupertypeWith B<in S32> is S<in S32>" {
                swCtx.parseType("A<in Any>").closestCommonSupertypeWith(swCtx.parseType("B<in S32>")) shouldBe swCtx.parseType("S<in S32>")
            }
        }

        "unify / subtype checking" {
            val swCtx = useValidModule("""
                interface S<T> {}
                interface D<T> : S<T> {}
            """.trimIndent())

            swCtx.parseType("D<S32>") should beAssignableTo(swCtx.parseType("S<S32>"))
            swCtx.parseType("D<S32>") should beAssignableTo(swCtx.parseType("S<out Any>"))
            swCtx.parseType("D<S32>") shouldNot beAssignableTo(swCtx.parseType("S<U32>"))

            swCtx.parseType("D<S32>") should beAssignableTo(swCtx.parseType("Any"))
            swCtx.parseType("Nothing") should beAssignableTo(swCtx.parseType("D<S32>"))
        }
    }
}}