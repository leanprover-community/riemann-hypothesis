module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
