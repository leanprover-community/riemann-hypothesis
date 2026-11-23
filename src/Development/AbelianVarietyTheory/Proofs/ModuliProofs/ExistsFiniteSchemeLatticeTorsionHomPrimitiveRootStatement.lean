module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.exists_finite_scheme_latticeTorsionHom_primitiveRoot : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  first | exact @GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | exact GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param | (intros; apply GlobalTheory.exists_latticeTorsionHom_primitiveRoot_param <;> assumption)
