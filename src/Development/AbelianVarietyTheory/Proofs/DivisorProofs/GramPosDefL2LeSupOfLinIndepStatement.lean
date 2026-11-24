module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  first | exact @GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | exact GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | (intros; apply GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound <;> assumption)
