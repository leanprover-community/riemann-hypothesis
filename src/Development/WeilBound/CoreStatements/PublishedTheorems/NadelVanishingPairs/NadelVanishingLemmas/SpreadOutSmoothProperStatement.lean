module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_smooth_proper : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_model_with_sections | exact _root_.GlobalTheory.LogPair.exists_model_with_sections | (intros; apply _root_.GlobalTheory.LogPair.exists_model_with_sections <;> assumption)
