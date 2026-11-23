module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataScalarsMemMaximalIdealTendstoZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

theorem _root_.GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.Mum.TensPolScal.scalars_tens | exact GlobalTheory.Mum.TensPolScal.scalars_tens | (intros; apply GlobalTheory.Mum.TensPolScal.scalars_tens <;> assumption)
