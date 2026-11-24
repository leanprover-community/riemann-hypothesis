module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthUpperBoundOddUnramifiedPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit (p : T.V) → y.IsAlg → p ≠ 2 → ¬ (p : ℤ) ∣ discr E → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → (SplitInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1)) : ℝ) : EReal)) ∧ (InertInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.FacUpOdd.nuFac_le_odd_unram | exact GlobalTheory.FacUpOdd.nuFac_le_odd_unram | (intros; apply GlobalTheory.FacUpOdd.nuFac_le_odd_unram <;> assumption)
