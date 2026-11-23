module

public import Development.EtaleCohomology.EtaleTrace.GenEtalePf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
