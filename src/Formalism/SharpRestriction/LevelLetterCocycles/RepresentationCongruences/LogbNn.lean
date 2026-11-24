module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA

lemma sg_eq (l h w S η : ℕ) : Sg l h w S η =
    (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 + (w:ℝ) * (l:ℝ)⁻¹ + (S:ℝ) * (l:ℝ)⁻¹ + (η:ℝ) * (l:ℝ)⁻¹ +
      Real.logb l (2 * (h:ℝ)) + 1 := by
  unfold Sg
  ring

lemma logb_nn (l h : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) : 0 ≤ Real.logb l (2 * (h:ℝ)) := by
  apply Real.logb_nonneg
  · have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  · have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    linarith

lemma sg_ge (l h w S η : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) :
    0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 ∧ 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ ∧
      0 ≤ (η:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ Real.logb l (2 * (h:ℝ)) ∧
      Real.logb l (2 * (h:ℝ)) + 1 + (η:ℝ) * (l:ℝ)⁻¹ ≤ Sg l h w S η ∧ 1 ≤ Sg l h w S η := by
  have hlg := logb_nn l h hl h1
  have a1 : 0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 := by positivity
  have a2 : 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a3 : 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a4 : 0 ≤ (η:ℝ) * (l:ℝ)⁻¹ := by positivity
  rw [sg_eq]
  refine ⟨a1, a2, a3, a4, hlg, by linarith, by linarith⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA
