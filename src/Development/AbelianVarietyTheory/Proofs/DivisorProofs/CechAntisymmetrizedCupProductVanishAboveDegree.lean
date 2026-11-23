module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem prodL_eq_zero_of_card {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) (t : Finset ι)
    (ht : vs.length + 1 < t.card) : prodL f h vs t = 0 := by
  induction vs generalizing t with
  | nil =>
    simp only [prodL, List.foldr_nil, oneC]
    simp only [List.length_nil] at ht
    rw [if_neg (by omega)]
  | cons v vs ih =>
    change Lop f h v (prodL f h vs) t = 0
    simp only [List.length_cons] at ht
    unfold Lop
    split_ifs with h1 h2
    · have e1 := ih t (by omega)
      have e2 := ih (t.erase (t.min' h1))
        (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega)
      rw [e1, e2, mul_zero, smul_zero, smul_zero, add_zero]
    · have e1 := ih t (by omega)
      rw [e1, mul_zero, smul_zero, add_zero]
    · rfl

theorem alt_and_phi_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]

end GlobalTheory.DI
