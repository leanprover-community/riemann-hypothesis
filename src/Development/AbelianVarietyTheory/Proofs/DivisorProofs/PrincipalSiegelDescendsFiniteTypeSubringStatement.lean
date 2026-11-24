module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelDescendsFiniteTypeSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principalSiegel_descends_finiteType_subring : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (R₀ : Subring R) (β₀ : cycAway n →+* R₀) (c₀ : SiegPre g n (zetaAway n) (spMap β₀)), Algebra.FiniteType ℤ R₀ ∧ R₀.subtype.comp β₀ = β ∧ c₀.Principal ∧ SiegPB c c₀ (spMap R₀.subtype) := by
  first | (exact @GlobalTheory.SiegFG.siegPre_descends_fg) | (exact GlobalTheory.SiegFG.siegPre_descends_fg) | (intros; apply GlobalTheory.SiegFG.siegPre_descends_fg  <;> assumption)
