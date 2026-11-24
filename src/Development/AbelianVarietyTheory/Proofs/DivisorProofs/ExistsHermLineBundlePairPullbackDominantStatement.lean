module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominant
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_hermLineBundlePair_pullback_dominant : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ P : Pair p, ∃ (Q : Pair q) (e : X.functionField →+* Y.functionField), Q.L = P.L.pull π hπ ∧ Q.A = P.A.pull π hπ ∧ ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map π hπ _ y) f := by
  first | exact @GlobalTheory.HSAmp.pair_pull | exact GlobalTheory.HSAmp.pair_pull | (intros; apply GlobalTheory.HSAmp.pair_pull <;> assumption)
