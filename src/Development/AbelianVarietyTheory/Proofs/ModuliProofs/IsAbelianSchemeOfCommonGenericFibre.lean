module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isAbelianScheme_of_common_generic_fibre
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B G : Over (Sp V)) [GrpObj B] [GrpObj G] (hB : IsAbelianScheme B) (hG : IsSemiAbelian G)
    (hext : ∀ f : (Over.pullback (spMap (algebraMap V K))).obj B ⟶ (Over.pullback (spMap (algebraMap V K))).obj G,
      IsMonHom f → ∃ F : B ⟶ G, (Over.pullback (spMap (algebraMap V K))).map F = f)
    (A : Over (Sp K)) [GrpObj A] {φ₁ : A.left ⟶ B.left} {φ₂ : A.left ⟶ G.left}
    (h₁ : IsGrpPullback A B (spMap (algebraMap V K)) φ₁) (h₂ : IsGrpPullback A G (spMap (algebraMap V K)) φ₂) :
    IsAbelianScheme G := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B (spMap (algebraMap V K))) h₁
  obtain ⟨e', he', -⟩ := grpPullback_iso h₂ (isGrpPullback_pullback G (spMap (algebraMap V K)))
  obtain ⟨F, hF⟩ := hext (e.hom ≫ e'.hom) inferInstance
  refine isAbelianScheme_of_generically_surjective V K B G hB hG F ?_
  rintro x ⟨k, hk⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk.symm
  have hsq : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G.hom (spMap (algebraMap V K)) =
      pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left := by
    simp
  rw [hF] at hsq
  have hid : (e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Iso.trans_hom, Iso.inv_hom_id, Over.id_left]
  refine ⟨pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z), ?_⟩
  calc F.left (pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z))
      = ((e ≪≫ e').inv.left ≫ pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left) z := rfl
    _ = ((e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left ≫ pullback.fst G.hom (spMap (algebraMap V K))) z := by rw [hsq]
    _ = pullback.fst G.hom (spMap (algebraMap V K)) z := by rw [← Category.assoc, hid, Category.id_comp]
    _ = x := hz

theorem goodRedExt_of_isDiscreteValuationRing :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K := by
  intro hext E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy hex
  obtain ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, h𝒜, -, -, hp1, hp2, -⟩ := hex
  obtain ⟨y', t, m, hy's, hy'j, hab⟩ := GlobalTheory.model_point_extends E H D l Xo c O β Y V K b y hy
  refine ⟨y', hy's, hy'j, hab ?_⟩
  have hm := m.cart
  have hc := IsGrpPullback.comp hp2 Y.m.cart
  have hw : (φ₂ ≫ Y.m.cm.F) ≫ Y.t.G.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ y' := by
    rw [hc.1.w, Category.assoc, hy'j]; rfl
  have h2 : IsGrpPullback A t.G (spMap (algebraMap V K)) (hm.1.lift _ _ hw) :=
    IsGrpPullback.cancel hm (hc.congr (by rw [hy'j]; rfl) (hm.1.lift_fst _ _ hw).symm) (hm.1.lift_snd _ _ hw)
  exact isAbelianScheme_of_common_generic_fibre 𝒜 t.G h𝒜 t.semi
    (fun f hf => (hext V K 𝒜 t.G (isSemiAbelian_of_isAbelianScheme 𝒜 h𝒜) t.semi f hf).exists.imp fun _ h => h.2)
    A hp1 h2

end GlobalTheory
