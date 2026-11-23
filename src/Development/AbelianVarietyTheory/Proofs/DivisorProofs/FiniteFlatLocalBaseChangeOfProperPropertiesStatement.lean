module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)
