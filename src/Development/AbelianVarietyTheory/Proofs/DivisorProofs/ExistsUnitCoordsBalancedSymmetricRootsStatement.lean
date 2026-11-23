module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRoots
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  first | exact @GlobalTheory.UnitForm.exists_unit_coords | exact GlobalTheory.UnitForm.exists_unit_coords | (intros; apply GlobalTheory.UnitForm.exists_unit_coords <;> assumption)
