module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GeometricAbelianConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareXiIntersection
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.algebraic_square_xi_intersection : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ T : Fin (d + 1) → HermLine Q.ιW, (∀ j, IsSmoothHerm (T j)) → II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₀ (Fin.cons X₀ T)) - II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons X₁ (Fin.cons X₁ T)) = 2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ T : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection | exact GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_square_xi_intersection <;> assumption)
