module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDepthSumRoundingOscillation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.productDepth_sum_rounding_oscillation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (cx : Lt1 Dw → ℕ), (∀ A B : Lt1 Dw → ℝ, (∀ f, FacBetween Xo la f (cx f) (A f) (B f)) → NuBetween Xo la cx (∑ f, A f) (∑ f, B f) ∧ ∃ n : ℕ, NuBetween Xo la cx n (n + (∑ f, (B f - A f) + 1))) ∧ ∀ b : ℝ, OscLe Xo c p cx b → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Comp Xo c), (letI := H.starRing; eLoc Y Z la cx ≤ (b : EReal)) := by
  first | exact @GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | exact GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le | (intros; apply GlobalTheory.RefSum.nuBetween_sum_and_eLoc_le <;> assumption)
