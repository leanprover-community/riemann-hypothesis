module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem madens_hess {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E ≃L[ℝ] E) (φ : E → ℝ) (y u v : E) :
    fderiv ℝ (fderiv ℝ (φ ∘ c)) y u v = fderiv ℝ (fderiv ℝ φ) (c y) (c u) (c v) := by
  set e : (E →L[ℝ] ℝ) ≃L[ℝ] (E →L[ℝ] ℝ) := c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) with he
  have h1 : fderiv ℝ (φ ∘ c) = e ∘ fderiv ℝ φ ∘ c := by
    funext z
    rw [c.comp_right_fderiv]
    ext w
    simp [he]
  rw [h1, e.comp_fderiv, c.comp_right_fderiv]
  simp [he]

theorem madens_cx (D : ℕ) (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    cxHessian (fun y' => φ (fun i => starRingEnd ℂ (y' i))) y =
      (cxHessian φ (fun i => starRingEnd ℂ (y i))).map (starRingEnd ℂ) := by
  let c : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := ContinuousLinearEquiv.piCongrRight (fun _ => Complex.conjCLE)
  have hc : ∀ z, c z = fun i => starRingEnd ℂ (z i) := fun z => rfl
  have hf : (fun y' : Fin D → ℂ => φ (fun i => starRingEnd ℂ (y' i))) = φ ∘ c := by
    funext z; simp [hc]
  have h1 : ∀ i : Fin D, c (Pi.single i 1) = Pi.single i 1 := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have h2 : ∀ i : Fin D, c (Complex.I • Pi.single i 1) = -(Complex.I • Pi.single i 1) := by
    intro i; funext k; rw [hc]; by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  ext i j
  simp only [cxHessian, Matrix.map_apply, hf, madens_hess, h1, h2, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  rw [hc y]
  generalize fderiv ℝ (fderiv ℝ φ) (fun i => starRingEnd ℂ (y i)) = H
  simp only [map_div₀, map_add (f := _), map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem c_madens : ∀ (D : ℕ) (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ), maDensity (fun j y' => φ j (fun i => starRingEnd ℂ (y' i))) y = maDensity φ (fun i => starRingEnd ℂ (y i)) := by
  intro D φ y
  have key : ∀ A : Fin D → Matrix (Fin D) (Fin D) ℂ,
      mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
    intro A

    simp only [mixedDisc, map_mul, map_div₀, map_one, map_natCast, map_sum, map_pow, map_neg]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.sum_apply]
  simp only [maDensity, madens_cx, key, Complex.conj_re]

end PositivityTheory.UnitarySelfGeneration
