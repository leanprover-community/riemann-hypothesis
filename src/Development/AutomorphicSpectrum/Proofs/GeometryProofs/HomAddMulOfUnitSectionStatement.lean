module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

theorem _root_.GlobalTheory.T.hom_add_mul_of_unit_section : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | exact GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed <;> assumption)
