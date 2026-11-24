module

public import Mathlib.Analysis.Analytic.Basic
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
