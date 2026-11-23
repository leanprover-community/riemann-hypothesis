module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
