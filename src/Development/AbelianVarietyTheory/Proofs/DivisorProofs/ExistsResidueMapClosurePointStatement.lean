module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_residueMap_closure_point : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (z : X) (k : ℕ),
  topologicalKrullDim (closure ({z} : Set X)) = k →
  ∃ (κ : Type) (_ : Field κ) (_ : Algebra ℂ κ) (π₀ : locRing z →+* κ),
    Function.Surjective π₀ ∧ (∀ r : locRing z, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) ∧
    (∀ a (h : Cartier.constFn p a ∈ locRing z), π₀ ⟨Cartier.constFn p a, h⟩ = algebraMap ℂ κ a) ∧
    (∃ w : Fin k → κ, TrBasis (algebraMap ℂ κ) w) ∧
    ∀ (x : X) (h : locRing x ≤ locRing z), IsLocModel (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range ∧
      (∀ f : κ, ∃ a b : locRing x, π₀ (Subring.inclusion h b) ≠ 0 ∧ f * π₀ (Subring.inclusion h b) = π₀ (Subring.inclusion h a)) ∧
      (IsClosed ({x} : Set X) → RatRes (algebraMap ℂ κ) (π₀.comp (Subring.inclusion h)).range) := by
  first | exact @GlobalTheory.ResMap.residueMap | exact GlobalTheory.ResMap.residueMap | (intros; apply GlobalTheory.ResMap.residueMap <;> assumption)
