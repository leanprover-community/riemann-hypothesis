module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
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
import Mathlib.Order.CompletePartialOrder
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff


set_option backward.isDefEq.respectTransparency.types false in
theorem of_isPullback_openImmersions (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {X T : Scheme.{0}} (φ : X ⟶ T) {ι : Type u} {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : T, ∃ i y, f i y = x)
    {Z : ι → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (q : ∀ i, Z i ⟶ V i)
    (H : ∀ i, IsPullback (k i) (q i) φ (f i)) (hq : ∀ i, P (q i)) : P φ := by
  have hU : iSup (fun i => (f i).opensRange) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun i => ?_
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange φ (f i))).mpr ?_
  rw [← (H i).isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr (hq i)

set_option backward.isDefEq.respectTransparency.types false in
theorem good_of_cover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  intro A B _ _ _ r T ι V f hf hcov g I hG
  have H : ∀ i, IsPullback (pullback.snd (bc A B g (f i)) I.subschemeι)
      (pullback.fst (bc A B g (f i)) I.subschemeι ≫ pullback.snd _ (f i ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) (f i) := fun i =>
    (IsPullback.of_hasPullback (bc A B g (f i)) I.subschemeι).flip.paste_vert
      (isPullback_bc A B g (f i))
  have e : ∀ i, (I.comap (bc A B g (f i))).subschemeι ≫ pullback.snd _ (f i ≫ g) =
      (I.comapIso (bc A B g (f i))).hom ≫ (pullback.fst (bc A B g (f i)) I.subschemeι ≫
        pullback.snd _ (f i ≫ g)) := fun i => by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hfin : ∀ i, IsFinite (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @IsFinite.{0}] at h
    exact h
  have hfl : ∀ i, Flat (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).2.1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @Flat.{0}] at h
    exact h
  have : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance
  have h1 : IsFinite (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @IsFinite.{0} _ f hcov _ _ H hfin
  have h2 : Flat (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @Flat.{0} _ f hcov _ _ H hfl
  refine ⟨h1, h2, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := hcov y
  have h := (hG i).2.2 y'
  rw [e i, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (H i) y'] at h
  exact h

end GlobalTheory.HilbAff
