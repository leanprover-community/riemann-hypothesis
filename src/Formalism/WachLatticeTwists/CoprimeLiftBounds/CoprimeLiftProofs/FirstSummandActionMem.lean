module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section T1
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

lemma first_summand_action_mem (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) (g : G) (b : FirstSummandSubmodule O e₁) :
    ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)) ∈ FirstSummandSubmodule O e₁ := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp b.2
  rw [LinearMap.mulLeft_apply] at hx
  show _ ∈ LinearMap.range (LinearMap.mulLeft O e₁)
  rw [LinearMap.mem_range]
  refine ⟨((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (x * r g⁻¹)), ?_⟩
  rw [LinearMap.mulLeft_apply, mul_smul_comm, mul_smul_comm, ← mul_assoc, hx]

def firstSummandRep (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) : Representation O G (FirstSummandSubmodule O e₁) where
  toFun g :=
    { toFun := fun b => ⟨_, first_summand_action_mem O r χ e₁ ε g b⟩
      map_add' := fun b b' => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (((b : A) + (b' : A)) * r g⁻¹)) = _ + _
        rw [add_mul, smul_add, smul_add])
      map_smul' := fun c b => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((c • (b : A)) * r g⁻¹)) =
          c • (((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)))
        rw [smul_mul_assoc, smul_comm _ c, smul_comm _ c]) }
  map_one' := LinearMap.ext fun b => Subtype.ext (by
    show ((ε 1 : Oˣ) : O) • (((χ 1 : T'ˣ) : T') • ((b : A) * r 1⁻¹)) = (b : A)
    simp)
  map_mul' g h := LinearMap.ext fun b => Subtype.ext (by
    show ((ε (g * h) : Oˣ) : O) • (((χ (g * h) : T'ˣ) : T') • ((b : A) * r (g * h)⁻¹)) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') •
        ((((ε h : Oˣ) : O) • (((χ h : T'ˣ) : T') • ((b : A) * r h⁻¹))) * r g⁻¹))
    rw [map_mul, map_mul, mul_inv_rev, map_mul, Units.val_mul, Units.val_mul, smul_mul_assoc,
      smul_mul_assoc, mul_smul, mul_smul, mul_assoc,
      smul_comm ((χ g : T'ˣ) : T') ((ε h : Oˣ) : O)])

end T1

theorem t1 : FirstSummandRepresentation := by
  intro O A T' G _ _ _ _ _ _ r χ e₁ ε
  exact ⟨firstSummandRep O r χ e₁ ε, fun g b => rfl⟩

end Formalism.RepresentationBoundsCohomology.BR
