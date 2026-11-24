module

public import Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf
