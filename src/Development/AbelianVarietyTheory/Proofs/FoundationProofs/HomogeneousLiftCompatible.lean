module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem homogeneous_lift_compatible : ∀ (l : ℕ) [Fact l.Prime] (w : ℕ) (p : (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))), (∀ n, (p n).IsHomogeneous w) → (∀ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (p (n + 1)) = p n) → ∃ q : MvPolynomial (Fin 2) ℤ_[l], q.IsHomogeneous w ∧ (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q = p n) ∧ ∀ q' : MvPolynomial (Fin 2) ℤ_[l], (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q' = p n) → q' = q := by
  intro l _ w p hhom hcomp
  have hc1 : ∀ (m : Fin 2 →₀ ℕ) (n : ℕ),
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) ((p (n + 1)).coeff m) = (p n).coeff m := by
    intro m n
    rw [← hcomp n, MvPolynomial.coeff_map]
  have hc : ∀ (m : Fin 2 →₀ ℕ) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁)) ((p k₂).coeff m) = (p k₁).coeff m := by
    intro m k₁ k₂ hk
    induction k₂, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [← ih, ← hc1 m k]
      show _ = ((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)))) _
      rw [ZMod.castHom_comp]

  let f : ∀ k, MvPolynomial (Fin 2 →₀ ℕ) ℤ →+* ZMod (l ^ k) := fun k =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun m => (p k).coeff m)
  have hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply MvPolynomial.ringHom_ext
    · intro r; simp [f]
    · intro m
      simp only [f, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hc m k₁ k₂ hk
  let g := PadicInt.lift hf
  let c : (Fin 2 →₀ ℕ) → ℤ_[l] := fun m => g (MvPolynomial.X m)
  have hcn : ∀ m n, PadicInt.toZModPow n (c m) = (p n).coeff m := by
    intro m n
    have := congrArg (fun φ => φ (MvPolynomial.X m)) (PadicInt.lift_spec hf n)
    simpa [c, g, f] using this
  have hdeg : ∀ m, c m ≠ 0 → m.degree = w := by
    intro m hm
    by_contra hne
    apply hm
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, map_zero]
    by_contra h0
    apply hne
    rw [Finsupp.degree_eq_weight_one]
    exact hhom n h0
  have hfin : (Function.support c).Finite :=
    (Finsupp.finite_of_degree_le w).subset fun m hm => le_of_eq (hdeg m hm)
  let q : MvPolynomial (Fin 2) ℤ_[l] := ∑ m ∈ hfin.toFinset, MvPolynomial.monomial m (c m)
  have hq : ∀ m, q.coeff m = c m := by
    intro m
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro m hm
    rw [hq] at hm
    have h := hdeg m hm
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  · intro n
    ext m
    rw [MvPolynomial.coeff_map, hq, hcn]
  · intro q' hq'
    apply MvPolynomial.ext
    intro m
    rw [hq]
    refine (PadicInt.ext_of_toZModPow (p := l)).mp fun n => ?_
    rw [hcn, ← hq' n, MvPolynomial.coeff_map]

end GlobalTheory.KZ.H3
