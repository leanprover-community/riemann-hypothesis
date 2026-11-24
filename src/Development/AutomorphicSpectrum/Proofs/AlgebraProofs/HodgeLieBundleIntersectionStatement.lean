module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersection
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.hodge_lie_bundle_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main <;> assumption)
