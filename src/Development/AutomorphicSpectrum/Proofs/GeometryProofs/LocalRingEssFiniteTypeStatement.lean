module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteType
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

theorem _root_.GlobalTheory.T.local_ring_ess_finite_type : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k), (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing
