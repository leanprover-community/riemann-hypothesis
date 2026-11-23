module

public import ReciprocityTheory.NeutralLocalFields.Duality
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Obar : ValuationSubring (PadicAlgCl p) := (PadicAlgCl.valued p).v.valuationSubring

abbrev kbar : Type := IsLocalRing.ResidueField (Obar p)

variable {p} in
theorem mem_Obar_iff {x : PadicAlgCl p} : x ∈ Obar p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe]
  rfl

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

noncomputable def resK : Subfield (kbar p) where
  toSubring := (K.toSubring.comap (Obar p).subtype).map (IsLocalRing.residue (Obar p))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases h0 : IsLocalRing.residue (Obar p) a = 0
    · rw [h0, inv_zero]; exact Subring.zero_mem _
    · have h0 := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 h0
      obtain ⟨u, rfl⟩ := h0
      refine ⟨((u⁻¹ : (Obar p)ˣ) : Obar p), ?_, ?_⟩
      · have h1 : (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = ((u : Obar p) : PadicAlgCl p)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have h2 : ((((u⁻¹ : (Obar p)ˣ) : Obar p) * (u : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
            rw [u.inv_mul]; rfl
          exact h2
        change (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) ∈ K
        rw [h1]
        exact K.inv_mem ha
      · apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, u.inv_mul, map_one]

noncomputable def qK : ℕ := Nat.card (resK p K)

noncomputable def Kn (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}

def IsFrobOn (n : ℕ) (φ : GK p K) : Prop :=
  ∀ x ∈ Kn p K n, ‖x‖ ≤ 1 → ‖φ x - x ^ qK p K‖ < 1

end ReciprocityTheory.DiscreteGroups.LocalClassField
