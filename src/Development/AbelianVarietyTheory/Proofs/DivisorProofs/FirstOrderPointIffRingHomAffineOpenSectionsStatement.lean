module

public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  first | exact @GlobalTheory.SchRing.deformation_on_sections | exact GlobalTheory.SchRing.deformation_on_sections | (intros; apply GlobalTheory.SchRing.deformation_on_sections <;> assumption)
