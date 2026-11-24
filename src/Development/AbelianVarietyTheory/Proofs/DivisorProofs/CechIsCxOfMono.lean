module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem cech_isCx_of_mono : ∀ (k : Type) [Field k] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module k E]
    (A : Finset ι → Submodule k E), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (cech A).IsCx := by
  intro k _ ι _ E _ _ A hA n a ha
  have ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · show GlobalTheory.DI.delta a ∈ cechC A (n + 1)
    refine Submodule.mem_pi.2 fun t _ => ?_
    show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _
    split_ifs with ht
    · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exact hA _ _ h2.1 (Finset.erase_subset _ _) h
      · rw [Submodule.mem_bot] at h; rw [h]; exact zero_mem _
    · rw [Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exfalso
        apply ht
        refine ⟨⟨i, hi⟩, ?_⟩
        have h3 := Finset.card_erase_add_one hi
        have h4 := h2.2
        omega
      · rw [Submodule.mem_bot] at h; rw [h, smul_zero]
  · exact GlobalTheory.DI.delta_delta a

end GlobalTheory.PD
