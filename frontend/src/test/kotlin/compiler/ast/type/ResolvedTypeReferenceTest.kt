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

import compiler.CoreIntrinsicsModule
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFileRootContext
import compiler.binding.type.BuiltinAny
import compiler.binding.type.BuiltinArray
import compiler.binding.type.RootResolvedTypeReference
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class ResolvedTypeReferenceTest : FreeSpec() { init {
    "Given a type hierarchy A; B : A; C : A, Z; D : A, Z; E : A, Z" - {
        val typeA = fakeType("A")
        val typeB = fakeType("B", typeA)
        val typeC = fakeType("C", typeA)

        val mutableA = typeA.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyA = mutableA.withMutability(TypeMutability.READONLY)
        val immutableA = readonlyA.withMutability(TypeMutability.IMMUTABLE)

        val mutableB = typeB.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyB = mutableB.withMutability(TypeMutability.READONLY)
        val immutableB = readonlyB.withMutability(TypeMutability.IMMUTABLE)

        val mutableC = typeC.baseReference.withMutability(TypeMutability.MUTABLE)
        val readonlyC = mutableC.withMutability(TypeMutability.READONLY)
        val immutableC = readonlyC.withMutability(TypeMutability.IMMUTABLE)

        "the closest common ancestor of" - {
            "mutable B and mutable A is mutable A" {
                mutableA.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableA) shouldBe mutableA
            }

            "mutable B and readonly A is readonly A" {
                readonlyA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "mutable B and immutable A is readonly A" {
                immutableA.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "readonly B and mutable A is readonly A" {
                mutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "readonly B and readonly A is readonly A" {
                readonlyA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "readonly B and immutable A is readonly A" {
                immutableA.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableA) shouldBe readonlyA
            }

            "immutable B and mutable A is readonly A" {
                mutableA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableA) shouldBe readonlyA
            }

            "immutable B and readonly A is readonly A" {
                readonlyA.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyA) shouldBe readonlyA
            }

            "immutable B and immutable A is immutable A" {
                immutableA.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableA) shouldBe immutableA
            }

            //----

            "mutable B and mutable C is mutable A" {
                mutableC.closestCommonSupertypeWith(mutableB) shouldBe mutableA
                mutableB.closestCommonSupertypeWith(mutableC) shouldBe mutableA
            }

            "mutable B and readonly C is readonly A" {
                readonlyC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "mutable B and immutable C is readonly A" {
                immutableC.closestCommonSupertypeWith(mutableB) shouldBe readonlyA
                mutableB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "readonly B and mutable C is readonly A" {
                mutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "readonly B and readonly C is readonly A" {
                readonlyC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "readonly B and immutable C is readonly A" {
                immutableC.closestCommonSupertypeWith(readonlyB) shouldBe readonlyA
                readonlyB.closestCommonSupertypeWith(immutableC) shouldBe readonlyA
            }

            "immutable B and mutable C is readonly A" {
                mutableC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(mutableC) shouldBe readonlyA
            }

            "immutable B and readonly C is readonly A" {
                readonlyC.closestCommonSupertypeWith(immutableB) shouldBe readonlyA
                immutableB.closestCommonSupertypeWith(readonlyC) shouldBe readonlyA
            }

            "immutable B and immutable C is immutable A" {
                immutableC.closestCommonSupertypeWith(immutableB) shouldBe immutableA
                immutableB.closestCommonSupertypeWith(immutableC) shouldBe immutableA
            }
        }
    }

    "generics" - {
        val swCtx = SoftwareContext()
        swCtx.registerModule(CoreIntrinsicsModule.NAME)
        CoreIntrinsicsModule.amendCoreModuleIn(swCtx)
        val context = swCtx.getPackage(CoreIntrinsicsModule.NAME)!!.moduleContext.sourceFiles.single().context

        "mutability projection" - {
            for (outerMutability in TypeMutability.entries) {
                val type = context.resolveType(
                    TypeReference(
                    simpleName = "Array",
                    mutability = outerMutability,
                    arguments = listOf(TypeArgument(TypeVariance.UNSPECIFIED, TypeReference("Any")))
                )
                ) as RootResolvedTypeReference

                "projects onto type parameters with $outerMutability" {
                    type.arguments.single().type.mutability shouldBe outerMutability
                }
            }
        }
    }
}}