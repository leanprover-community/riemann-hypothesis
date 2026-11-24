module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeTrivialMod
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.wedge_line_lattice_trivial_mod : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E) (ϖ : Ω), IsCptGen ξ → ϖ ≠ 0 → (∀ x, ϖ ∈ regAt ξ x) → A.IsVB p V → B.IsVB q V' → a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt A B p q a b x f) → ExactModLat A B ϖ (p + q) → TrivMod (lineLat A B p q a b) ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | exact GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DddTriv.trivMod_lineLat <;> assumption)
