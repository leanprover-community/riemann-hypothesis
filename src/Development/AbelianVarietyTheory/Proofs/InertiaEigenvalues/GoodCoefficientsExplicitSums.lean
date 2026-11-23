module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem adicSpan_smul_top_mem_iff {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (x : O) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule O O) ↔ ∃ b : O, x = ϖ ^ n * b := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩

theorem adicComplete_explicit_sums {O : Type} [CommRing O] (ϖ : O)
    [h : IsAdicComplete (Ideal.span {ϖ}) O] :
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (M := O)
      (fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j) (by
        intro m n hmn
        rw [SModEq.sub_mem, adicSpan_smul_top_mem_iff]
        refine ⟨-∑ j ∈ Finset.Ico m n, ϖ ^ (j - m) * x j, ?_⟩
        rw [← Finset.sum_range_add_sum_Ico _ hmn, mul_neg, Finset.mul_sum]
        have : ∑ j ∈ Finset.Ico m n, ϖ ^ m * (ϖ ^ (j - m) * x j)
            = ∑ j ∈ Finset.Ico m n, ϖ ^ j * x j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
        rw [this]; ring)
    refine ⟨L, fun n => ?_⟩
    have h1 := (SModEq.sub_mem.mp (hL n))
    rw [adicSpan_smul_top_mem_iff] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨-b, by rw [mul_neg, ← hb]; ring⟩
  · refine IsHausdorff.haus' (I := Ideal.span {ϖ}) a fun n => ?_
    rw [SModEq.zero, adicSpan_smul_top_mem_iff]
    exact ha n

theorem goodO_coeff_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O,
      a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  intro l _ LL _ _ _ O _ _ hG
  have hc := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.2.2
  exact adicComplete_explicit_sums (h := hc) ((l : ℕ) : O)

end GlobalTheory
