module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChange
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.exists_triangular_regular_frame_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted <;> assumption)
