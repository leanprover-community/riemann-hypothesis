module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_surjective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (U : T.affineOpens) : Function.Surjective (kappa A B g I U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (str A B) g) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hle : (⊤ : Subring Γ(pullback (str A B) g, W)) ≤
      (kappa A B g I U).range.comap (I.subschemeι.app W).hom := by
    rw [← hgen, Subring.closure_le]
    rintro _ (⟨z, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1 ⊗ₜ (Scheme.ΓSpecIso (CommRingCat.of B)).hom z, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, one_mul, Iso.hom_inv_id_apply]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rfl
    · refine ⟨c ⊗ₜ 1, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, mul_one]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      rfl
  intro y
  obtain ⟨x, hx⟩ := I.subschemeι_app_surjective ⟨W, hW⟩ y
  obtain ⟨w, hw⟩ := hle (Subring.mem_top x)
  exact ⟨w, hw.trans hx⟩

end GlobalTheory.HilbAff
