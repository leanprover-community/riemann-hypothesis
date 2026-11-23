module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLift
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseLift

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg


theorem _root_.GlobalTheory.T.torsion_point_valuation_ring_lift : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (w : G.left), IsClosed ({w} : Set G.left) → ∃ (N : ℕ) (O : ValuationSubring (AlgebraicClosure L)) (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ G), 1 ≤ N ∧ y ^ N = 1 ∧ y.left (IsLocalRing.closedPoint O) = w ∧ ∀ a : 𝓞 L, ((ρ a : O) : AlgebraicClosure L) = algebraMap L (AlgebraicClosure L) (a : L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.exists_torsion_point_reducing_to <;> assumption)
