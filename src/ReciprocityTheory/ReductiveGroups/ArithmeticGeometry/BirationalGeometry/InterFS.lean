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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]

theorem mixedDisc_one (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ => f) y = (fderiv ℝ (fderiv ℝ f) y (Pi.single 0 1) (Pi.single 0 1) +
      fderiv ℝ (fderiv ℝ f) y (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1)) /
        (2 * Real.pi) := by
  have hre : ∀ u v : ℝ, ((((u : ℂ) + Complex.I * (v : ℂ)) / 4).re) = u / 4 := by
    intro u v
    simp [Complex.div_ofNat_re]
  rw [maDensity, mixedDisc_one]
  simp only [cxHessian, hre]
  have := Real.pi_pos
  simp
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
