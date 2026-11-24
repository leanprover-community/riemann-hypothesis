module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace UpperTheory.V.Z.Sym.Glob

open Loc

section

variable {F : Type} [Field F] {Δ τ : F}

private theorem re_mul_star (x : Lsq F Δ) : (x * star x).re = x.re ^ 2 - Δ * x.im ^ 2 := by
  simp
  ring

private theorem nrm_nonneg (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) : 0 ≤ σ (x * star x).re := by
  rw [re_mul_star]
  simp only [map_sub, map_mul, map_pow]
  nlinarith [sq_nonneg (σ x.re), sq_nonneg (σ x.im)]

private theorem nrm_pos (σ : F →+* ℝ) (h : σ Δ < 0) (x : Lsq F Δ) (hx : x ≠ 0) : 0 < σ (x * star x).re := by
  rw [re_mul_star, map_sub, map_mul, map_pow, map_pow]
  have hne : x.re ≠ 0 ∨ x.im ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (QuadraticAlgebra.ext (by simp [hc.1]) (by simp [hc.2]))
  have ha := mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ x.im))
  have hb := sq_nonneg (σ x.re)
  rcases hne with h1 | h1
  · have h2 : σ x.re ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    nlinarith
  · have h2 : σ x.im ≠ 0 := (map_ne_zero σ).mpr h1
    have h3 : 0 < σ x.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
    have h4 := mul_pos (neg_pos.mpr h) h3
    nlinarith

private theorem herm_re (c t : F) (m : EL Δ τ) (x : Sp Δ τ) :
    (herm c (t • m) x x).re = c * (x.1 * star x.1).re + t * (herm 1 m (0, x.2) (0, x.2)).re := by
  simp [herm]
  ring

private theorem sum_pos (σ : F →+* ℝ) (h : σ Δ < 0) (y : Fin 3 → Lsq F Δ) (hy : y ≠ 0) :
    0 < σ (∑ i, y i * star (y i)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have h0 := nrm_nonneg σ h (y 0)
  have h1 := nrm_nonneg σ h (y 1)
  have h2 := nrm_nonneg σ h (y 2)
  have hp := nrm_pos σ h (y i) hi
  rw [Fin.sum_univ_three, QuadraticAlgebra.re_add, QuadraticAlgebra.re_add, map_add (f := _), map_add (f := _)]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hp h1) h2
  · exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos h0 hp) h2
  · exact add_pos_of_nonneg_of_pos (add_nonneg h0 h1) hp

end

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.posLaw :
    UpperTheory.V.Z.Sym.Glob.PosLaw := by
  intro F _ _ Δ D hD τ d m hm c t
  have hneg := hD.neg
  refine ⟨fun hc ht x hx σ => ?_, fun δ ι P hM => ?_⟩
  · rw [herm_re, map_add (f := _), map_mul, map_mul]
    have h1 := nrm_nonneg σ (hneg σ) x.1
    by_cases h2 : x.2 = 0
    · have hx1 : x.1 ≠ 0 := by
        intro h1'
        exact hx (Prod.ext h1' h2)
      have h4 := nrm_pos σ (hneg σ) x.1 hx1
      have h3 : (herm 1 m (0, x.2) (0, x.2)).re = 0 := by
        rw [h2]
        simp [herm]
      rw [h3, map_zero, mul_zero, add_zero]
      exact mul_pos (hc σ) h4
    · have hx2 : ((0 : Lsq F Δ), x.2) ≠ 0 := by
        intro h'
        exact h2 (congrArg Prod.snd h')
      have h4 := hm _ hx2 σ
      nlinarith [hc σ, ht σ, mul_nonneg (hc σ).le h1, mul_pos (ht σ) h4]
  · have key : ∀ x : Sp Δ τ, x ≠ 0 → TPos (herm c (t • m) x x).re := by
      intro x hx σ
      rw [hM.form x x]
      apply sum_pos σ (hneg σ)
      intro h0
      exact hx (P.injective (h0.trans (map_zero P).symm))
    refine ⟨fun σ => ?_, fun σ => ?_⟩
    · have h1 := key ((1 : Lsq F Δ), 0) (by simp) σ
      simpa [herm] using h1
    · have hx : ((0 : Lsq F Δ), (1 : EL Δ τ)) ≠ 0 := by simp
      have h1 := key _ hx σ
      have h2 : 0 < σ (herm 1 m (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2) (0, ((0 : Lsq F Δ), (1 : EL Δ τ)).2)).re := hm _ hx σ
      have hz : ((0 : Lsq F Δ) * star (0 : Lsq F Δ)).re = 0 := by simp
      rw [herm_re, map_add (f := _), map_mul, map_mul] at h1
      simp only [hz, map_zero, mul_zero, zero_add] at h1
      nlinarith
