module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_deformation_base_ring_local_domain : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  first | exact @GlobalTheory.MBLow.ring_of_deformation | exact GlobalTheory.MBLow.ring_of_deformation | (intros; apply GlobalTheory.MBLow.ring_of_deformation <;> assumption)
