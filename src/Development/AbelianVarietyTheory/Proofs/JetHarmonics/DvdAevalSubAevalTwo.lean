module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem dvd_aeval_sub_aeval_two {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a u w u' w' : A) (hu : a ∣ u - u') (hw : a ∣ w - w') (P : MvPolynomial (Fin 2) K) :
    a ∣ MvPolynomial.aeval ![u, w] P - MvPolynomial.aeval ![u', w'] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have := dvd_add hp hr
    simp only [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p i hp =>
    have hi : a ∣ (![u, w] i) - (![u', w'] i) := by
      fin_cases i
      · simpa using hu
      · simpa using hw
    have := dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem X_pow_succ_dvd_of_DT {q : ℕ} [Fact q.Prime] (f : ℂ_[q]⟦X⟧) (n : ℕ)
    (h0 : constantCoeff f = 0) (hD : (X : ℂ_[q]⟦X⟧) ^ n ∣ DT f) :
    (X : ℂ_[q]⟦X⟧) ^ (n + 1) ∣ f := by
  have hu : IsUnit (1 + X : ℂ_[q]⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  unfold DT at hD
  rw [hu.dvd_mul_left, X_pow_dvd_iff] at hD
  rw [X_pow_dvd_iff]
  intro m hm
  cases m with
  | zero => simpa using h0
  | succ k =>
    have := hD k (by omega)
    rw [coeff_derivative] at this
    have hk : ((k : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hk

theorem ode_unique : ∀ (q : ℕ) [Fact q.Prime] (P₁ P₂ : MvPolynomial (Fin 2) ℂ_[q]) (u w u' w' : ℂ_[q]⟦X⟧), DT u = MvPolynomial.aeval ![u, w] P₁ → DT w = MvPolynomial.aeval ![u, w] P₂ → DT u' = MvPolynomial.aeval ![u', w'] P₁ → DT w' = MvPolynomial.aeval ![u', w'] P₂ → constantCoeff u = constantCoeff u' → constantCoeff w = constantCoeff w' → u = u' ∧ w = w' := by
  intro q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw
  have hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g := by
    intro f g
    unfold DT
    rw [map_sub, mul_sub]
  have key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hu, sub_self]
        · rw [hsub, h1, h3]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hw, sub_self]
        · rw [hsub, h2, h4]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
  constructor
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)

end GlobalTheory.MomOne
