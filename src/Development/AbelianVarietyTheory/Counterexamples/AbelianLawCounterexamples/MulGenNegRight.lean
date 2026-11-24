module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.TrivialBiextension

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BiextSignTwist

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

end

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left

def LawIsCube (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) : Prop :=
  ∀ (J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι) (j : thK → L.L.ι),
    (∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I') →
    LB.Coh L.L (thφ G (x3 G)) j →
    (∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I') →
    res (inf_le_left : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (law.s J) =
    res (inf_le_right : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (c.t.s j)

section Trivial
open GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension (trivLB pull_one mul_one' corr_one isGen_one)

end Trivial

end GlobalTheory.BiextSignTwist
