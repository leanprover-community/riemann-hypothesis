module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
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

theorem _root_.GlobalTheory.T.regularNonvanishingLocusSection_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (g : X.functionField), g ∈ P.H a b → IsOpen (NV P a b g) ∧ (genericPoint X ∈ NV P a b g ↔ g ≠ 0) ∧ (∀ n : ℕ, 1 ≤ n → NV P (n * a) (n * b) (g ^ n) = NV P a b g) ∧ (∀ f ∈ P.H a b, ∀ z ∈ NV P a b g, RegAt z (f / g) ∧ (z ∈ NV P a b f ↔ UnitAt z (f / g))) ∧ ∀ f ∈ P.H a b, ∀ (σ : k →+* ℂ) (y : CxPts p σ), under y ∈ NV P a b g → P.nu a b σ y f = ‖ratVal (f / g) y‖ * P.nu a b σ y g ∧ 0 < P.nu a b σ y g := by
  first | exact @GlobalTheory.HSAmp.nv_rules | exact GlobalTheory.HSAmp.nv_rules | (intros; apply GlobalTheory.HSAmp.nv_rules <;> assumption)
