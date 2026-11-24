module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlobalSectionsDimNefPowTensorAmpleIsBi
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

theorem _root_.GlobalTheory.T.lbH0_nef_pow_tens_ample_le_mul_pow_dim : GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] (Z : Scheme.{0}) [Algebra F Γ(Z, ⊤)] (d : ℕ), IsProjOver (strHom F (X := Z)) → topologicalKrullDim Z ≤ d → ∀ L A : LB Z, IsNef F L → IsAmpleLB A → ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, (lbH0 F (tens (lbPow L m) A) : ℝ) ≤ C * (m : ℝ) ^ d := by
  first | exact @GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | exact GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO | (intros; apply GlobalTheory.NefGrowth.lineBundleGlobalSectionsDim_nefPow_tensor_ample_isBigO <;> assumption)
