module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


open GlobalTheory.Heat in
theorem GlobalTheory.Heat.ringOp_conj_pow_gen : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  intro Ω _ _ n d δ Θ h2 u p p' c hc
  have hs : ∀ (s : Finset (Fin n)) (D : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
    intro s D x
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  refine ⟨d - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ a c / c)) • δ b - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ b c / c)) • δ a, u,
    p + d c / c - (1 / 2) * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c),
    p' - (1 / 2) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c) + ∑ a, u a * (δ a c / c), ?_, ?_⟩
  · intro y hy
    rw [Derivation.sub_apply, Derivation.sub_apply, hs, hs, Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero, sub_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
  · intro k f
    have e1 : ∀ b, δ b (c ^ k * f) = c ^ k * (δ b f + (k : FractionRing Ω) * (δ b c / c) * f) :=
      fun b => fractionField_derivation_pow_mul_logDeriv (δ b) hc k f
    have e2 : ∀ a b, δ a (δ b (c ^ k * f)) = c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f) := by
      intro a b
      rw [e1, fractionField_derivation_pow_mul_logDeriv (δ a) hc]
      simp only [map_add (f := _), Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
      ring
    have e3 : d (c ^ k * f) = c ^ k * (d f + (k : FractionRing Ω) * (d c / c) * f) := fractionField_derivation_pow_mul_logDeriv d hc k f
    unfold ringOp
    simp only [e2, e3]
    simp only [e1, Derivation.sub_apply, hs, Derivation.smul_apply, smul_eq_mul]
    have hL : ∑ a, ∑ b, Θ a b * (c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f)) =
        c ^ k * (∑ a, ∑ b, Θ a b * δ a (δ b f) + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
          + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
          + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c)
          + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hU : ∑ a, u a * (c ^ k * (δ a f + (k : FractionRing Ω) * (δ a c / c) * f)) =
        c ^ k * (∑ a, u a * δ a f + (k : FractionRing Ω) * f * ∑ a, u a * (δ a c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hD1 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ a c / c) * δ b f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hD2 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ b c / c) * δ a f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hh : (2 : FractionRing Ω) * (1 / 2) = 1 := mul_one_div_cancel h2
    rw [hL, hU, hD1, hD2]
    linear_combination (c ^ k * ((k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
      + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
      + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)
      + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c))) * hh
