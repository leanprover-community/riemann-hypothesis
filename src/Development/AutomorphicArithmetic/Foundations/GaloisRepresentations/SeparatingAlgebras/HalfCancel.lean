module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Gen

private lemma factor_eq {a b t : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) (hat : a - t * b ≠ 0) :
    (a - t * b) / (a - b) * ((1 - a⁻¹ / b⁻¹) / (1 - t * (a⁻¹ / b⁻¹))) = 1 := by
  have e : a⁻¹ / b⁻¹ = b / a := by field_simp
  rw [e]
  have h1 : 1 - b / a = (a - b) / a := by field_simp
  have h2 : 1 - t * (b / a) = (a - t * b) / a := by field_simp
  rw [h1, h2]
  field_simp

private lemma half_cancel (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) (w : Fin n → ℂˣ)
    (hw : Function.Injective w) (hn : ∀ i, ‖(w i : ℂ)‖ = 1) :
    (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) / ((w p.1 : ℂ) - (w p.2 : ℂ))) *
      half (t : ℂ) w⁻¹ = 1 := by
  unfold half
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun p hp => ?_)
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hne : p.1 ≠ p.2 := hp.ne
  refine factor_eq (w p.1).ne_zero (w p.2).ne_zero ?_ ?_
  · intro h
    exact hne (hw (Units.ext (sub_eq_zero.mp h)))
  · intro h
    have h' : (w p.1 : ℂ) = (t : ℂ) * (w p.2 : ℂ) := sub_eq_zero.mp h
    have hn' := congrArg norm h'
    rw [norm_mul, hn, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at hn'
    linarith

theorem rDens_pf : RFormula → DensSymm → RDens := by
  intro hR hS n t h0 h1 l z hz hn
  rw [hR n (t : ℂ) l z hz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw : Function.Injective (z ∘ σ) := hz.comp σ.injective
  have hwn : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hn (σ i)
  have hc := half_cancel n t h0 h1 (z ∘ σ) hw hwn
  rw [← hS n (t : ℂ) z σ]
  unfold dens
  simp only [Function.comp_apply] at hc
  calc _ = monomialChar l (z ∘ σ) * half (t : ℂ) (z ∘ σ) * ((∏ p ∈ prs n, ((z (σ p.1) : ℂ) - (t : ℂ) * (z (σ p.2) : ℂ)) / ((z (σ p.1) : ℂ) - (z (σ p.2) : ℂ))) * half (t : ℂ) (z ∘ σ)⁻¹) := by ring
    _ = _ := by rw [hc, mul_one]

end UpperTheory.Gal.Gen

end
