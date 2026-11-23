module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
