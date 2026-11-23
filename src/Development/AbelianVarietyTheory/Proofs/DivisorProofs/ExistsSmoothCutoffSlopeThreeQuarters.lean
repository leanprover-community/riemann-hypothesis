module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_isCut (T : ℝ) : ∃ θ : ℝ → ℝ, IsCut T θ := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, ReciprocityTheory.L2DbarEstimates.I.IsCutoff χ :=
    ⟨_, ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi⟩
  obtain ⟨hs, h1, h0, hb, hd⟩ := hχ
  set a : ℝ → ℝ := fun x => (x + T + 1) / 4 + 1 / 2 with ha
  have haS : ContDiff ℝ ∞ a := by
    simp only [ha]; fun_prop
  have hda : ∀ x, HasDerivAt a (1 / 4) x := by
    intro x
    have := (((hasDerivAt_id x).add_const T).add_const 1).div_const 4
    simpa [ha] using this.add_const (1 / 2)
  refine ⟨χ ∘ a, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.comp haS
  · intro x hx
    exact h1 _ (by simp only [ha]; linarith)
  · intro x hx
    exact h0 _ (by simp only [ha]; linarith)
  · intro x
    exact hb _
  · intro x
    have hχd : DifferentiableAt ℝ χ (a x) :=
      (hs.differentiable (by simp)) _
    have hD : HasDerivAt (χ ∘ a) (deriv χ (a x) * (1 / 4)) x :=
      hχd.hasDerivAt.comp x (hda x)
    rw [hD.deriv, abs_mul]
    have := hd (a x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith

theorem exists_isCut₂ : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := exists_isCut

end GlobalTheory
