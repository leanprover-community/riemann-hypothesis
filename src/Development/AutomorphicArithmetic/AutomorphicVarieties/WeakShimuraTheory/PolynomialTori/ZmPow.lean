module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section

variable {O : Type} [CommRing O] {Γ : Type} [Group Γ] {R : Type} [CommRing R] [Algebra O R] (ρ : Γ →* M4 R)

private lemma zm_one : (1 : R) ∈ Submodule.span O (mono ρ 0) :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

private lemma zm_mul {v w : ℤ × ℤ} {x y : R} (hx : x ∈ Submodule.span O (mono ρ v))
    (hy : y ∈ Submodule.span O (mono ρ w)) : x * y ∈ Submodule.span O (mono ρ (v + w)) := by
  open scoped Pointwise in
  have hsub : mono ρ v * mono ρ w ⊆ mono ρ (v + w) := by
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨M, hM, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp [hL, hM], by simp⟩
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hsub h

private lemma zm_pow {v : ℤ × ℤ} {x : R} (hx : x ∈ Submodule.span O (mono ρ v)) (k : ℕ) :
    x ^ k ∈ Submodule.span O (mono ρ (k • v)) := by
  induction k with
  | zero => simpa using zm_one (O := O) ρ
  | succ k ih => rw [pow_succ, succ_nsmul]; exact zm_mul ρ ih hx

end

theorem UpperTheory.V.Ws.Po.zMono :
    ∀ (O : Type) [CommRing O] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R] (ρ : Γ →* M4 R) (W : WPres O (ℤ × ℤ) R)
      (c : Γ → Fin 4 → Fin 4 → O), (∀ g a b, a ≠ b → c g a b = 0) →
      (∀ i, ∃ g a b, W.z i = ρ g a b - algebraMap O R (c g a b) ∧ W.wt i = wt a b) →
      ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ Algebra.adjoin O (mono ρ 0) := by
  intro O _ Γ _ R _ _ ρ W c hc hz n hn
  have hmem : ∀ i, W.z i ∈ Submodule.span O (mono ρ (W.wt i)) := by
    intro i
    obtain ⟨g, a, b, hzi, hwi⟩ := hz i
    rw [hzi, hwi]
    by_cases hab : a = b
    · subst hab
      have h0 : wt a a = 0 := (wt_eq_zero a a).mpr rfl
      rw [h0, Algebra.algebraMap_eq_smul_one]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨[(g, a, a)], by simp [h0], by simp⟩) ?_
      exact Submodule.smul_mem _ _ (zm_one ρ)
    · rw [hc g a b hab, map_zero, sub_zero]
      exact Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩
  classical
  have hall : ∀ t : Finset W.σ,
      (∏ s ∈ t, W.z s ^ n s) ∈ Submodule.span O (mono ρ (∑ s ∈ t, n s • W.wt s)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using zm_one (O := O) ρ
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact zm_mul ρ (zm_pow ρ (hmem a) _) ih
  have h := hall n.support
  rw [Finsupp.weight_apply, Finsupp.sum] at hn
  rw [hn] at h
  exact Algebra.span_le_adjoin O _ h
