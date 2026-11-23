module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def transferMap {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ⟶ pullback z g :=
  pullback.map z' g' z g eZ.hom (𝟙 T) eS.hom hsq.symm (by rw [Category.id_comp, hg])

instance {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    IsIso (transferMap z z' eS eZ hsq g' g hg) := by
  unfold transferMap; infer_instance

def transferIso {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    pullback z' g' ≅ pullback z g :=
  asIso (transferMap z z' eS eZ hsq g' g hg)

lemma transferIso_hom_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).hom ≫ pullback.snd z g = pullback.snd z' g' := by
  simp only [transferIso, asIso_hom, transferMap]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma transferIso_inv_snd {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g) :
    (transferIso z z' eS eZ hsq g' g hg).inv ≫ pullback.snd z' g' = pullback.snd z g := by
  rw [Iso.inv_comp_eq, transferIso_hom_snd]

lemma transferIso_map {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z)
    (hsq : eZ.hom ≫ z = z' ≫ eS.hom) {T H : Scheme.{0}} (g' : T ⟶ S') (g : T ⟶ S) (hg : g' ≫ eS.hom = g)
    (h' : H ⟶ S') (f : T ⟶ H) (hf' : f ≫ h' = g') (hf : f ≫ (h' ≫ eS.hom) = g) :
    pullback.map z' g' z' h' (𝟙 Z') f (𝟙 S') (by simp) (by rw [Category.comp_id, hf'])
        ≫ (transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl).hom =
      (transferIso z z' eS eZ hsq g' g hg).hom ≫
        pullback.map z g z (h' ≫ eS.hom) (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf]) := by
  simp only [transferIso, asIso_hom, transferMap, pullback.map]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem isHilbRep_transfer : ∀ {S Z S' Z' : Scheme.{0}} (z : Z ⟶ S) (z' : Z' ⟶ S') (eS : S' ≅ S) (eZ : Z' ≅ Z),
    eZ.hom ≫ z = z' ≫ eS.hom → ∀ r : ℕ, IsHilbRep z' r → IsHilbRep z r := by
  intro S Z S' Z' z z' eS eZ hsq r hrep
  obtain ⟨H, h', U, u', hP, hC, hF, hFl, hR, hU⟩ := hrep
  set ΦH := transferIso z z' eS eZ hsq h' (h' ≫ eS.hom) rfl with hΦH
  have eu : (u' ≫ ΦH.hom) ≫ pullback.snd z (h' ≫ eS.hom) = u' ≫ pullback.snd z' h' := by
    rw [Category.assoc, transferIso_hom_snd]
  refine ⟨H, h' ≫ eS.hom, U, u' ≫ ΦH.hom, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [eu]; exact hF
  · rw [eu]; exact hFl
  · rw [eu]; exact hR
  intro T g V v hv hvF hvFl hvR
  have hg : (g ≫ eS.inv) ≫ eS.hom = g := by simp
  set ΦT := transferIso z z' eS eZ hsq (g ≫ eS.inv) g hg with hΦT
  have ev : (v ≫ ΦT.inv) ≫ pullback.snd z' (g ≫ eS.inv) = v ≫ pullback.snd z g := by
    rw [Category.assoc, transferIso_inv_snd]
  have hv' : IsClosedImmersion (v ≫ ΦT.inv) := inferInstance
  obtain ⟨f, ⟨hf', w, hpb⟩, huniq⟩ := hU T (g ≫ eS.inv) V (v ≫ ΦT.inv) hv' (by rw [ev]; exact hvF)
    (by rw [ev]; exact hvFl) (by rw [ev]; exact hvR)
  have hf : f ≫ (h' ≫ eS.hom) = g := by rw [← Category.assoc, hf', hg]
  refine ⟨f, ⟨hf, w, ?_⟩, ?_⟩
  · refine hpb.of_iso (Iso.refl _) ΦT (Iso.refl _) ΦH ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f hf' hf
    · simp
  · rintro f₂ ⟨hf₂, w₂, hpb₂⟩
    have hf₂' : f₂ ≫ h' = g ≫ eS.inv := by rw [← hf₂]; simp
    apply huniq f₂ ⟨hf₂', w₂, ?_⟩
    refine hpb₂.of_iso (Iso.refl _) ΦT.symm (Iso.refl _) ΦH.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
        transferIso_map z z' eS eZ hsq (g ≫ eS.inv) g hg h' f₂ hf₂' hf₂, Iso.inv_hom_id_assoc]
    · simp [hΦH]

end GlobalTheory.HilbertSch
