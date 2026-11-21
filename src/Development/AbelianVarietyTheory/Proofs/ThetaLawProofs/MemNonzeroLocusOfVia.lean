import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUnique
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TorsSqMap
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitude
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvr

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.KeyKa

namespace GlobalTheory.KeyLine

section Via

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gs_unit_pow {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) (n : ℕ) :
    gs r z U (a.val ^ n) = (gm r z U a).val ^ n := by
  rw [← gs_unit r z U h, gs_eq r z U h, gs_eq r z U h, map_pow, map_pow]

theorem via_iff_stalk (w : LB.Iso L' (L.pull F)) (l : ℕ) (a' : ∀ i, Γ(X', L'.U i)) (a : ∀ j, Γ(X, L.U j)) :
    KeyVia.Via w l a' a ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (a j) = (gw w r z j k).val ^ l * gs r z _ (a' k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit_pow _ z _ hy _ l)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit_pow _ y _ hy _ l).symm

variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))} {l : ℕ}
  {a : ∀ j, Γ(X, L.U j)} {a' : ∀ i, Γ(X', L'.U i)} {a'' : ∀ i, Γ(X'', L''.U i)}

theorem via_comp (T : Tri w w' w'') (hL' : L'.IsLB) (h : KeyVia.Via w l a' a) (h' : KeyVia.Via w' l a'' a') :
    KeyVia.Via w'' l a'' a := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z j k hj hk => ?_
  obtain ⟨i, hi⟩ := exists_chart hL' (F' (q z))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h' Z q z i k hi hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, e', Units.val_mul, mul_pow, _root_.mul_assoc]

theorem via_cancel (T : Tri w w' w'') (hL : L.IsLB) (h : KeyVia.Via w l a' a) (h'' : KeyVia.Via w'' l a'' a) :
    KeyVia.Via w' l a'' a' := by
  refine (via_iff_stalk _ _ _ _).2 fun Z q z i k hi hk => ?_
  obtain ⟨j, hj⟩ := exists_chart hL (F (F' (q z)))
  have e := (via_iff_stalk _ _ _ _).1 h Z (q ≫ F') z j i hj hi
  have e' := (via_iff_stalk _ _ _ _).1 h'' Z q z j k hj hk
  rw [T Z q z j i k hj hi hk, ← Category.assoc, e, Units.val_mul, mul_pow, _root_.mul_assoc] at e'
  exact ((Units.isUnit _).pow l).mul_left_cancel e'

end Via

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'} {x'' : KeyIn R''}
  {f : R →+* R'} {f' : R' →+* R''}

theorem keyVia_g {φ w} (h : KeyVia x' x f φ w) : x'.P.g = x.P.g := by
  obtain ⟨_, hg, _⟩ := h
  exact hg

theorem keyVia_isPullback {φ w} (h : KeyVia x' x f φ w) : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := by
  obtain ⟨_, _, _, h, _⟩ := h
  exact h.1

theorem keyVia_trans {φ w φ' w'} (H : KeyVia x' x f φ w) (H' : KeyVia x'' x' f' φ' w') :
    ∃ w'', KeyVia x'' x (f'.comp f) (φ' ≫ φ) w'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x' φ' w' s'' s' → SecVia x'' x (φ' ≫ φ) w'' s'' s := by
  obtain ⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' h h' => via_comp (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x'.P.isLB h h'⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem keyVia_cancel {φ w φ'' w''} (H : KeyVia x' x f φ w) (H'' : KeyVia x'' x (f'.comp f) φ'' w'') :
    ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ φ' ≫ φ = φ'' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s → SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := H''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp f f'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩, rfl,
    fun l s s' s'' h h'' => via_cancel (L := x.P.L) (L' := x'.P.L) (L'' := x''.P.L) (l := l) (a := s.f) (a' := s'.f) (a'' := s''.f) T x.P.isLB h h''⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyLine
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.basis_powerSections_local_baseChange : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (l : ℕ), 1 ≤ l → (∃ b : Fin (l ^ x.P.g) → RR x l, IsBasis x b) ∧ ∀ b : Fin (l ^ x.P.g) → RR x l, IsBasis x b → ∀ (R' : Type) [CommRing R'] (f : R →+* R') (x' : KeyIn R') φ w (b' : Fin (l ^ x.P.g) → RR x' l), KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' := by
  first | exact @GlobalTheory.KeyBasis.main | exact GlobalTheory.KeyBasis.main | (intros; apply GlobalTheory.KeyBasis.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2ComparisonNumber_baseChange_similitude_alt : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (b : Fin (m ^ x.P.g) → RR x m) (b' : Fin (m ^ x'.P.g) → RR x' m) (lam : Rˣ), al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b (k.cast (by rw [hg])))) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x' m al b' (Units.map f.toMonoidHom lam) := by
  first | exact @GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude | exact GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude | (intros; apply GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaFiniteUnit

theorem exists_common_field {L F E : Type} [Field L] [Field F] [Field E] (σ : L →+* F) (τ : L →+* E) :
    ∃ (Ω : Type) (_ : Field Ω) (i : F →+* Ω) (g : E →+* Ω), g.comp τ = i.comp σ := by
  letI := σ.toAlgebra
  letI := τ.toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct L F E)
  exact ⟨TensorProduct L F E ⧸ M, Ideal.Quotient.field M,
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeRight.toRingHom,
    RingHom.ext fun v => congrArg (Ideal.Quotient.mk M)
      (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := L) (A := F) (B := E)) v).symm⟩

theorem exists_complete_extension {O F : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
    (f : O →+* F) (hf : Function.Injective f) (S : Finset F) :
    ∃ (L : Type) (_ : Field L) (σ : L →+* F) (V : ValuationSubring L) (j₀ : O →+* V) (O' : Type) (_ : CommRing O')
      (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (c : V →+* O') (Ω : Type) (_ : Field Ω) (i : F →+* Ω) (g : O' →+* Ω),
      (∀ a ∈ S, a ∈ Set.range σ) ∧ σ.comp ((algebraMap V L).comp j₀) = f ∧ IsLocalHom (c.comp j₀) ∧
      Function.Injective g ∧ g.comp c = i.comp (σ.comp (algebraMap V L)) := by
  letI := f.toAlgebra
  haveI : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 hf
  letI := FractionRing.liftAlgebra O F
  let L := IntermediateField.adjoin (FractionRing O) (S : Set F)
  haveI : Algebra.EssFiniteType (FractionRing O) L :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite S.finite_toSet)
  haveI : Algebra.EssFiniteType O (FractionRing O) := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors O)
  haveI : Algebra.EssFiniteType O L := Algebra.EssFiniteType.comp O (FractionRing O) L
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 fun a b h => hf (congrArg Subtype.val h)
  obtain ⟨V, hV, hle⟩ := exists_discreteValuationSubring_dominating_of_essFiniteType (R := O) (L := L)
    (IsDiscreteValuationRing.not_isField O)
  obtain ⟨hm, hloc⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ V).1 hle
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hc : Function.Injective (algebraMap V O') := algebraMap_adicCompletion_injective_of_dvr V
  have hc' : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap V O')) :=
    (IsFractionRing.injective O' _).comp hc
  let τ : L →+* FractionRing O' := IsFractionRing.lift (A := V) hc'
  obtain ⟨Ω, _, i, g, hg⟩ := exists_common_field (algebraMap L F) τ
  refine ⟨L, inferInstance, algebraMap L F, V, (algebraMap O L).codRestrict V hm, O', inferInstance, inferInstance,
    inferInstance, inferInstance, algebraMap V O', Ω, inferInstance, i, g.comp (algebraMap O' _), fun a ha => ?_,
    RingHom.ext fun _ => rfl, RingHom.isLocalHom_comp _ _, g.injective.comp (IsFractionRing.injective O' _),
    RingHom.ext fun v => ?_⟩
  · exact ⟨⟨a, IntermediateField.subset_adjoin _ _ ha⟩, rfl⟩
  · have e : algebraMap O' (FractionRing O') (algebraMap V O' v) = τ (algebraMap V L v) :=
      (IsFractionRing.lift_algebraMap hc' v).symm
    change g (algebraMap O' (FractionRing O') (algebraMap V O' v)) = i (algebraMap L F (algebraMap V L v))
    rw [e]
    exact RingHom.congr_fun hg _

theorem exists_points_extension {O F : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
    (f : O →+* F) (hf : Function.Injective f) {X : Scheme.{0}} (π : X ⟶ Sp O) [IsProper π] {T : Type} [Finite T]
    (p : T → (Sp F ⟶ X)) (hp : ∀ a, p a ≫ π = spMap f) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (j : O →+* O') (Ω : Type) (_ : Field Ω) (i : F →+* Ω)
      (g : O' →+* Ω), IsLocalHom j ∧ Function.Injective g ∧ g.comp j = i.comp f ∧
      ∀ a, ∃ q : Sp O' ⟶ X, q ≫ π = spMap j ∧ spMap g ≫ q = spMap i ≫ p a := by
  classical
  haveI := Fintype.ofFinite T
  choose S hS using fun a => KaLift.exists_finset_descend π f (p a) (hp a)
  obtain ⟨L, _, σ, V, j₀, O', _, _, _, _, c, Ω, _, i, g, h₁, h₂, h₃, h₄, h₅⟩ :=
    exists_complete_extension f hf (Finset.univ.biUnion S)
  refine ⟨O', _, ‹_›, ‹_›, ‹_›, c.comp j₀, Ω, _, i, g, h₃, h₄, ?_, fun a => ?_⟩
  · rw [← RingHom.comp_assoc, h₅, ← h₂]
    rfl
  · obtain ⟨q₁, e₁, e₂⟩ := hS a L σ _ h₂ fun b hb => h₁ b (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hb⟩)
    obtain ⟨q₂, e₃, e₄⟩ := exists_valuativeExtension (V := V) (K := L) π (spMap j₀) q₁ (e₂.trans (spMap_comp _ _))
    have e₅ : spMap (algebraMap V L) ≫ q₂ = q₁ := e₃
    refine ⟨spMap c ≫ q₂, by rw [Category.assoc, e₄, spMap_comp], ?_⟩
    rw [← Category.assoc, ← spMap_comp, h₅, spMap_comp, spMap_comp, Category.assoc, Category.assoc, e₅, e₁]

theorem finite_preimage_fibre {X X' S S' : Scheme.{0}} {φ : X' ⟶ X} {π' : X' ⟶ S'} {π : X ⟶ S} {t : S' ⟶ S}
    [LocallyOfFiniteType π] [QuasiCompact π] (h : IsPullback φ π' π t) {Z : Set X} (hZ : IsClosed Z) (hfin : Z.Finite)
    (p : S') : {y : X' | π' y = p ∧ φ y ∈ Z}.Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  haveI : Finite I.subscheme := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun y => (⟨I.subschemeι y, hr.le ⟨y, rfl⟩⟩ : Z))
      fun a b e => I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val e)
  haveI : LocallyQuasiFinite (I.subschemeι ≫ π) := .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have hp := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert h
  haveI : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ π') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hp ‹_›
  haveI : QuasiCompact (pullback.snd I.subschemeι φ ≫ π') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance
  refine (((pullback.snd I.subschemeι φ ≫ π').finite_preimage_singleton p).image
    (pullback.snd I.subschemeι φ)).subset fun y hy => ?_
  obtain ⟨a, ha⟩ := hr.ge hy.2
  obtain ⟨b, -, hb⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback I.subschemeι φ) a y ha
  exact ⟨b, (congrArg π' hb).trans hy.1, hb⟩

theorem mul_transpose_of_transpose_mul {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) this.symm
  have e : (al * al.transpose - (m : ℤ) • 1) * al = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]
  have e' := congrArg (· * al.adjugate) e
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.zero_mul, Matrix.mul_smul, Matrix.mul_one] at e'
  exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_left hd)

theorem pow_eq_one_of_ker {G : Type} [CommGroup G] {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (ξ : Fin 4 → G)
    (hξ : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : Fin 4) : ξ r ^ m = 1 := by
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = 1 := by simp [hξ]
  have e₂ : ∀ r', ∏ c, (ξ r' ^ al r' c) ^ al r c = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
    have := congrFun (congrFun (mul_transpose_of_transpose_mul hm h) r') r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      _root_.mul_one, mul_zero] at this
    rw [← this]
    simp only [← zpow_mul, Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]
  simp only [← Finset.prod_zpow] at e
  rw [Finset.prod_comm] at e
  simp only [e₂] at e
  rw [Finset.prod_eq_single r (fun b _ hb => by simp [hb]) (by simp)] at e
  simpa using e

theorem keyVia_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ' w'} (H : KeyVia x' x f φ w)
    (H' : KeyVia x'' x' f' φ' w') : ∃ w'', KeyVia x'' x (f'.comp f) (φ' ≫ φ) w'' ∧
      ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l), SecVia x' x φ w s' s → SecVia x'' x' φ' w' s'' s' →
        SecVia x'' x (φ' ≫ φ) w'' s'' s := by
  obtain ⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' h h' j k hle => fn_ext fun y hy => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl
  · obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' y)
    have hj : φ (φ' y) ∈ x.P.L.U (j PUnit.unit) := mem_pull (F := φ' ≫ φ).1 hy.1
    have a := KeyBasis.via_val (w := w) (n := l) (a' := s'.f) (a := s.f) h (𝟙 _ ≫ φ') y hj hi
    have b := KeyBasis.via_val (w := w') (n := l) (a' := s''.f) (a := s'.f) h' (𝟙 _) y hi hy.2
    have t := T _ (𝟙 _) y (j PUnit.unit) i k hj hi hy.2
    rw [b, ← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, ← t] at a
    refine (gs_appLE (φ' ≫ φ) _ _ hle (𝟙 _) y hy _).trans (a.trans ?_)
    refine Eq.trans (congrArg₂ (· * ·) ?_ (gs_res _ y _ hy _).symm) (gs_mul _ y _ hy _ _).symm
    let v : Γ(x''.P.A.left, (x.P.L.pull (φ' ≫ φ)).U j ⊓ x''.P.L.U k)ˣ := w''.s (j, k)
    exact ((congrArg (gs (𝟙 _) y _) (Units.val_pow_eq_pow_val v l).symm).trans
      ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_pow _ _ _)))).symm

theorem exists_pull_hom {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'}
    {f : R →+* R'} {φ w} (H : KeyVia x' x f φ w) (hf : Function.Injective f) :
    ∃ h : Pt x →* Pt x', Function.Injective h ∧ ∀ z z', z' = h z ↔ z'.left ≫ φ = spMap f ≫ z.left := by
  choose h h₁ h₂ using ((KeyVia.main _ _ x x' f).2 φ w H).2.1
  obtain ⟨_, _, _, hp, -⟩ := H
  let D : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp R)) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨MonoidHom.mk' h fun a b => (h₂ _ _ ?_).symm, fun a b e => ?_, fun z z' => ⟨fun e => e ▸ h₁ z, h₂ z z'⟩⟩
  · have e := hp.2 _ (h a) (h b) (D ≫ a) (D ≫ b) (h₁ a).symm (h₁ b).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  · have e' : h a = h b := e
    haveI := x.P.isAb.proper
    haveI : IsDominant (spMap f) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)
      exact this⟩
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) (f := a.left) (g := b.left) x.P.A.hom
      ((Over.w a).trans (Over.w b).symm) (spMap f) ?_)
    exact (h₁ a).symm.trans ((congrArg (·.left ≫ φ) e').trans (h₁ b))

theorem eq_of_pow_eq_one (laws : Out.Laws) {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) {N : ℕ}
    (hN1 : 1 ≤ N) (hN : IsUnit (N : R)) {a b : Pt x} (ha : a ^ N = 1) (hb : b ^ N = 1) (p : Sp R) (h : a.left p = b.left p) :
    a = b := by
  obtain ⟨-, -, -, het, -⟩ := laws.mulN (Sp R) x.P _ hN1
  haveI := het (by
    have := hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this)
  haveI := x.P.isAb.proper
  have e₁ := KaLift.apply_closedPoint_eq x.P.A.hom a.left b.left (Over.w _) (Over.w _) p h
  have e₂ : spMap (IsLocalRing.residue R) (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have e₃ : ∀ c : Pt x, (spMap (IsLocalRing.residue R) ≫ c.left) ≫ x.P.A.hom = spMap (IsLocalRing.residue R) :=
    fun c => (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue R) ≫ ·) (Over.w c)).trans
      (Category.comp_id _))
  have e₄ := KaLift.eq_of_apply_eq x.P.A.hom _ IsLocalRing.residue_surjective _ _ (e₃ a) (e₃ b)
    ((congrArg a.left e₂).trans (e₁.trans (congrArg b.left e₂).symm))
  have e₅ : a ≫ Out.mulA x.P.A N = b ≫ Out.mulA x.P.A N := by
    rw [Out.mulA, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, ha, hb]
  exact Over.OverMorphism.ext (eq_of_isLocalRing_of_unramified (R := CommRingCat.of R) (Out.mulA x.P.A N).left
    (congrArg CommaMorphism.left e₅) (spMap (IsLocalRing.residue R)) ⟨_, e₂⟩ e₄)

open EtBaseChange in

theorem exists_unit_val_jac {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    {n : ℕ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n} {s' : Fin x'.P.g → RR x' n} (H : KeyVia x' x f φ w)
    (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) {z : Pt x} {z' : Pt x'}
    (hz : z'.left ≫ φ = spMap f ≫ z.left) {c c'} (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z'.left ⁻¹ᵁ x'.P.L.U c') :
    ∃ u : R'ˣ, (∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l), SecVia x' x φ w sg' sg →
      valT (T := R') z'.left (x'.P.L.U c') (sg'.f c') * (u : R') ^ l = f (valT (T := R) z.left (x.P.L.U c) (sg.f c))) ∧
      ((∀ i, valT (T := R') z'.left (x'.P.L.U c') ((s' i).f c') = 0) →
        jac x' s' z' c' * (u : R') ^ (x.P.g * n) = f (jac x s z c)) := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := H
  have hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [hz]
    exact h (show spMap f p ∈ ⊤ from trivial)
  have hW := le_inf_pull (T := R') z'.left c c' hφ h'
  let u : R'ˣ := Units.map (valH (T := R') z'.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := R') z'.left ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val = u :=
    valT_eq _ _ hW _
  refine ⟨u, fun l sg sg' hsg => ?_, fun hzero => ?_⟩
  · have e := valT_via (T := R') hsg z'.left c c' hφ h'
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := R') q (x.P.L.U c) (sg.f c)) hz).trans (valT_spMap f z.left h _)
  · have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v (k.cast hg)).left
        (x.P.L.U c) ((s (i.cast hg)).f c))) = (u : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z') * x'.v k).left (x'.P.L.U c') ((s' i).f c')) := fun i k => by
      have t := translate_comp hp F hF₁ z z' hz (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) h
      have l₂ := translate_le z' (x'.v k) (x'.basis.1 _) h'
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z') * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
        rw [t]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ c c' l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U c) ((s (i.cast hg)).f c)) t).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) h' _).trans (hzero i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) hW _).trans hu)
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm

theorem exists_chart_point {R : Type} [CommRing R] [IsLocalRing R] {x : KeyIn R} (z : Pt x) :
    ∃ i, ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i := by
  obtain ⟨i, hi⟩ := exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint R))
  exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩

theorem etZ_pull {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'}
    {φ w} {n d : ℕ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n} {s' : Fin x'.P.g → RR x' n} (H : KeyVia x' x f φ w)
    (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) {z : Fin d → Pt x} {z' : Fin d → Pt x'} {ch}
    (hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left) (E : EtZ x s z ch) : ∃ ch', EtZ x' s' z' ch' := by
  obtain ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩ := E
  choose ch' hch' using fun a => exists_chart_point (z' a)
  choose u hval hjac using fun a => exists_unit_val_jac hg H hs (hz' a) (hz₁ a) (hch' a)
  obtain ⟨_, _, F, hp, -⟩ := H
  have hzero : ∀ a i, valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval a n _ _ (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  refine ⟨ch', hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩
  · exact isUnit_of_mul_isUnit_left (hjac a (hzero a) ▸ (hz₃ a).map f)
  · refine hz₄ a a' h (spMap f p) ?_
    have e₁ := congrArg (fun q => q p) (hz' a)
    have e₂ := congrArg (fun q => q p) (hz' a')
    exact e₁.symm.trans ((congrArg φ e).trans e₂)
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) fun i h =>
      hy (i.cast hg.symm) (EtBaseChange.mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

theorem kaForm_map' {R R' : Type} [CommRing R] [CommRing R'] (F : Rˣ →* R'ˣ) (g n l l' : ℕ) (t t' J : Rˣ)
    (lam lam' : ℕ → Rˣ) : F (kaForm g n l l' t t' lam lam' J) =
      kaForm g n l l' (F t) (F t') (fun j => F (lam j)) (fun j => F (lam' j)) (F J) := by
  simp only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]

theorem via_mul' {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul' {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul' (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem torsSq_kosD_mul {R F : Type} [CommRing R] [Field F] (f : R →+* F) {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (ev' : ∀ j, Matrix (Fin d) (Fin (N j)) F) (Q : Matrix (Fin d) (Fin d) F) (t : R) (hQ : Q.det ≠ 0)
    (hev : ev' 0 = Q * (ev 0).map f) (hC : IsCx kdeg (kosD m ev)) (H : TorsSq kdeg (kosD m ev) t) :
    TorsSq kdeg (kosD (fun i j j' => (m i j j').map f) ev') (f t * Q.det ^ 2) := by
  have e : (kosD m ev).map f = kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f) := by
    ext p q
    rcases p with p | a <;> rcases q with ⟨I, k⟩ | b <;> simp [kosD, apply_ite f]
  obtain ⟨t, rfl⟩ := (TorsionUnique.torsSq_unique _ _ _ _ t t hC H H).2
  have H' := e ▸ torsSq_map R _ kdeg _ F f _ H
  have hC' : IsCx kdeg (kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f)) := by
    rw [← e]
    exact ⟨fun p q h => by rw [Matrix.map_apply, hC.1 p q h, map_zero],
      by rw [← Matrix.map_mul, hC.2, Matrix.map_zero _ (map_zero f)]⟩
  obtain ⟨P, rfl⟩ := (Matrix.isUnit_iff_isUnit_det Q).2 hQ.isUnit
  obtain ⟨t', h₁, h₂⟩ := torsSq_kosD_conj F g d N (fun i j j' => (m i j j').map f) (fun i j j' => (m i j j').map f)
    (fun j => (ev j).map f) ev' (fun _ => 1) P⁻¹ (Units.map f.toMonoidHom t) (fun i j _ => by simp)
    (by rw [hev, ← Matrix.mul_assoc, Units.inv_mul]; simp) hC' H'
  simp only [map_one, one_zpow, Finset.prod_const_one, _root_.mul_one, map_inv, inv_pow, mul_inv_eq_iff_eq_mul] at h₂
  rw [h₂] at h₁
  exact h₁

theorem exists_unit_kaVal (laws : Out.Laws) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {F : Type} [Field F] {f : O →+* F} {x : KeyIn O} {x' : KeyIn F}
    {φ w} {n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n}
    {s' : Fin x'.P.g → RR x' n} {d : ℕ} (hd : d = x'.P.g.factorial * n ^ x'.P.g) (z : Fin d → Pt x) {z' : Fin d → Pt x'}
    {ch'} (hO : ∀ m : ℕ, 1 ≤ m → IsUnit (m : O)) (hf : Function.Injective f) (hadm : admitted x.P.g n l l' al)
    (hx : KeyVia x' x f φ w) (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg)))
    (hfin : {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite)
    (E : EtZ x' s' z' ch') (hz : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left)
    (hξ : ∀ k, k = l ∨ k = l' → ∀ j ≤ x.P.g, ∃ ξ : (Fin 4 → Fin ((k - j * n) ^ x.P.g)) → Fin 4 → Pt x,
      Function.Injective ξ ∧ ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al (k - j * n) r c).prod = 1) :
    ∃ u : Oˣ, KaVal x' n l l' al s' (Units.map f.toMonoidHom u) := by
  subst hd
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn F := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  have hp : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := hx.choose_spec.choose_spec.choose_spec.1.1
  choose ch hch using fun a => exists_chart_point (z a)
  choose u hval hjac using fun a => exists_unit_val_jac (x := x) (x' := x') rfl hx hs (hz a) (hch a) (E.1 a)
  replace hjac := fun a => hjac a (E.2.1 a)
  have hzero : ∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0 := fun a i =>
    hf ((hval a n _ _ (hs i)).symm.trans ((congrArg (· * _) (E.2.1 a i)).trans ((zero_mul _).trans (map_zero f).symm)))
  have hne : ∀ a, f (jac x s (z a) (ch a)) ≠ 0 := fun a =>
    hjac a ▸ ((E.2.2.1 a).mul ((u a).isUnit.pow _)).ne_zero
  have hinj : Function.Injective z := fun a a' e => by
    by_contra h
    have e₂ : (z' a).left = (z' a').left := hp.hom_ext (by rw [hz, hz, e]) ((Over.w _).trans (Over.w _).symm)
    exact E.2.2.2.1 a a' h (IsLocalRing.closedPoint F) (by rw [e₂])
  have hcov : ∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      ∃ a, ∃ p : Sp O, (z a).left p = y := fun y hy₀ hy => by
    have e : x.P.A.hom y = spMap f (IsLocalRing.closedPoint F) := by
      refine PrimeSpectrum.ext ?_
      have e₁ : PrimeSpectrum.asIdeal (x.P.A.hom y) = (⊥ : Ideal O) := by
        by_contra h
        exact hy₀ (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
          (Ring.DimensionLEOne.maximalOfPrime h (PrimeSpectrum.isPrime _))))
      refine e₁.trans (Eq.symm ?_)
      change Ideal.comap f (IsLocalRing.maximalIdeal F) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective f hf
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y (IsLocalRing.closedPoint F) e
    obtain ⟨a, p, rfl⟩ := E.2.2.2.2 y' fun i h => hy i (KaLift.mem_nonzeroLocus_of_via (hs i) y' h)
    exact ⟨a, spMap f p, (congrArg (fun q => q p) (hz a)).symm⟩
  have hex := ((KeyVia.main O F x x' f).2 φ w hx).1
  let J : Fˣ := Units.mk0 (f (∏ a, jac x s (z a) (ch a))) (by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun a _ => hne a)
  have key : ∀ k, k = l ∨ k = l' → x.P.g * n < k →
      ∃ (b' : ∀ j, Fin ((k - j * n) ^ x.P.g) → RR x' (k - j * n)) (lam : ℕ → Oˣ) (t e : Oˣ) (dl : Fˣ),
        (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧
          IsSquareDeterminantComparison x' (k - j * n) (al (k - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧
        KosVal x' k s' z' ch' b' (Units.map f.toMonoidHom t * (∏ a, u a) ^ (-2 * (k : ℤ)) * dl ^ 2 : Fˣ) ∧
        J = Units.map f.toMonoidHom e * dl ^ 2 := by
    intro k hk hl
    have hpos : ∀ j ≤ x.P.g, 1 ≤ k - j * n := fun j hj => by
      have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      omega
    have hb : ∀ j, ∃ b : Fin ((k - j * n) ^ x.P.g) → RR x (k - j * n), ∃ lam : Oˣ, j ≤ x.P.g →
        IsBasis x b ∧ IsSquareDeterminantComparison x (k - j * n) (al (k - j * n)) b lam := fun j => by
      by_cases hj : j ≤ x.P.g
      · obtain ⟨b, hb⟩ := (T.basis_powerSections_local_baseChange laws O x (k - j * n) (hpos j hj)).1
        obtain ⟨ξ, h₁, h₂⟩ := hξ k hk j hj
        haveI := x.P.isAb.comm
        have h₃ : ∀ I r, ξ I r ^ (k - j * n) = 1 := fun I r =>
          pow_eq_one_of_ker (hpos j hj) (hadm.2.2.2 _) (ξ I) (fun c => (List.prod_ofFn).symm.trans (h₂ I c)) r
        obtain ⟨lam, hlam⟩ := T.exists_l2Val_field_or_dvr_split_kernel laws O x _ _ b ξ (hO _ (hpos j hj)) (hadm.2.2.2 _) hb (fun I I' hI p => by
          by_contra h
          refine hI (h₁ (funext fun r => ?_))
          exact eq_of_pow_eq_one laws x (hpos j hj) (hO _ (hpos j hj)) (h₃ I r) (h₃ I' r) p
            (not_not.1 fun h' => h ⟨r, h'⟩)) h₂
        exact ⟨b, lam, fun _ => ⟨hb, hlam⟩⟩
      · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, 1, fun h => absurd h hj⟩
    choose b lam hb using hb
    obtain ⟨m, hm⟩ := (KoszulCx.koszul_isCx O x n k _ s b z ch hl fun j hj => (hb j hj).1).1
    obtain ⟨ev, Pm, t, h₁, h₂, h₃, e, h₄⟩ := T.discriminant_eq_jacobian_complete_intersection_dvr laws O x n k _ s b m z ch (by have := hadm.1; omega) hl
      (fun j hj => (hb j hj).1) hm hfin hch hzero (fun a h => hne a (by rw [h, map_zero])) hinj hcov
    obtain ⟨t, rfl⟩ := (TorsionUnique.torsSq_unique _ _ _ _ t t h₂ h₃ h₃).2
    have hdl : f Pm.det ≠ 0 := fun h => J.ne_zero (by
      change f _ = 0
      rw [← h₄, map_mul, map_pow, h]; simp)
    choose b' hb' using fun j i => (hex _ (b j i)).exists
    refine ⟨b', lam, t, e, Units.mk0 _ hdl, fun j hj => ⟨?_, ?_⟩, ⟨fun i j j' => (m i j j').map f, fun i j hj i' => ?_, ?_⟩,
      Units.ext ?_⟩
    · exact (T.basis_powerSections_local_baseChange laws O x _ (hpos j hj)).2 (b j) (hb j hj).1 F f x' φ w (b' j) hx (hb' j)
    · exact T.l2ComparisonNumber_baseChange_similitude_alt O F x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2
    · have h₅ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      have h₆ : n + (k - (j + 1) * n) = k - j * n := by
        rw [Nat.add_mul, Nat.one_mul] at h₅ ⊢
        omega
      exact coords_mul' hx h₆ (hs i) (hb' (j + 1) i') (hb' j) (hm i j hj i')
    · have hdet : (Matrix.diagonal (fun a => (((u a ^ (k - 0 * n))⁻¹ : Fˣ) : F)) * Pm.map f).det =
          (((∏ a, u a) ^ (-(k : ℤ)) : Fˣ) : F) * f Pm.det := by
        rw [Matrix.det_mul, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_inv_distrib, Finset.prod_pow,
          RingHom.map_det, Nat.zero_mul, Nat.sub_zero, zpow_neg, zpow_natCast]
        rfl
      have H := torsSq_kosD_mul f m ev
        (fun j => Matrix.of fun a i => valT (T := F) (z' a).left (x'.P.L.U (ch' a)) ((b' j i).f (ch' a)))
        _ t (hdet ▸ mul_ne_zero (Units.ne_zero _) hdl) (by
          rw [Matrix.mul_assoc, ← Matrix.map_mul, ← h₁]
          ext a i
          rw [Matrix.diagonal_mul]
          refine ((Units.eq_inv_mul_iff_mul_eq _).2 ?_)
          exact (_root_.mul_comm _ _).trans ((congrArg _ (Units.val_pow_eq_pow_val _ _)).trans
            (hval a _ (b 0 i) (b' 0 i) (hb' 0 i)))) h₂ h₃
      have e₁ : (∏ a, u a) ^ (-2 * (k : ℤ)) = ((∏ a, u a) ^ (-(k : ℤ))) ^ 2 := by group
      rw [hdet, mul_pow, ← _root_.mul_assoc] at H
      rw [e₁]
      exact H
    · change f _ = f e * f Pm.det ^ 2
      rw [← h₄, map_mul, map_pow, _root_.mul_comm]
  obtain ⟨c, lam, t, e, dl, hc, hct, hJ⟩ := key l (Or.inl rfl) hadm.2.1
  obtain ⟨c₂, lam₂, t₂, e₂, dl₂, hc₂, hct₂, hJ₂⟩ := key l' (Or.inr rfl) (hadm.2.1.trans hadm.2.2.1)
  have hdl : dl₂ ^ 2 = Units.map f.toMonoidHom (e₂⁻¹ * e) * dl ^ 2 := by
    rw [map_mul, map_inv, _root_.mul_assoc, ← hJ, hJ₂, inv_mul_cancel_left]
  refine ⟨kaForm x.P.g n l l' t (t₂ * (e₂⁻¹ * e)) lam lam₂ e, z', ch', c, c₂, _, _,
    Units.map f.toMonoidHom e * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)) * dl ^ 2, _, _, E, ?_, hc, hc₂, hct, hct₂, ?_⟩
  · rw [mul_right_comm, ← hJ, zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq,
      Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact (Finset.prod_congr rfl fun a _ => hjac a).trans (map_prod f _ _).symm
  · have H := kaForm_homogeneous F x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom (t₂ * (e₂⁻¹ * e)))
      (Units.map f.toMonoidHom e) (∏ a, u a) 1 dl (fun j => Units.map f.toMonoidHom (lam j))
      (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H
    refine (kaForm_map' _ _ _ _ _ _ _ _ _ _).trans (H.symm.trans ?_)
    congr 1
    rw [hdl, map_mul _ t₂]
    ac_rfl

theorem isUnit_of_finite_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  intro laws O _ _ _ _ F _ f x xF φ w n l l' al hg s sF κ a e hf hadm hx hs hfin hκ ha _
  have hκ' := hκ
  obtain ⟨z, ch, b, b₂, -, -, -, lam, lam₂, E, -, hb, hb₂, -⟩ := hκ'
  have h₀ : ∀ k j : ℕ, ∃ S : Set (Pt xF), S.Finite ∧ (k = l ∨ k = l' → j ≤ xF.P.g →
      ∃ ξ : (Fin 4 → Fin ((k - j * n) ^ xF.P.g)) → Fin 4 → Pt xF, (∀ I r, ξ I r ∈ S) ∧
        Function.Injective ξ ∧ ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al (k - j * n) r c).prod = 1) := fun k j => by
    by_cases h : (k = l ∨ k = l') ∧ j ≤ xF.P.g
    · obtain ⟨c, la, ξ, -, -, -, -, h₁, h₂, -⟩ : ∃ c la, IsSquareDeterminantComparison xF (k - j * n) (al (k - j * n)) c la := by
        rcases h.1 with rfl | rfl
        exacts [⟨_, _, (hb j h.2).2⟩, ⟨_, _, (hb₂ j h.2).2⟩]
      refine ⟨Set.range fun p : _ × _ => ξ p.1 p.2, Set.finite_range _, fun _ _ => ⟨ξ, fun I r => ⟨(I, r), rfl⟩,
        fun I I' hI => ?_, h₂⟩⟩
      by_contra hne
      obtain ⟨r, hr⟩ := h₁ I I' hne (IsLocalRing.closedPoint F)
      exact hr (by rw [hI])
    · exact ⟨∅, Set.finite_empty, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose S hS hS' using h₀
  let A : Set (Pt xF) := Set.range z ∪ ⋃ j ∈ Set.Iic xF.P.g, (S l j ∪ S l' j)
  haveI : Finite A := ((Set.finite_range z).union
    ((Set.finite_Iic _).biUnion fun j _ => (hS l j).union (hS l' j))).to_subtype
  haveI := x.P.isAb.proper
  have hp : IsPullback φ xF.P.A.hom x.P.A.hom (spMap f) := hx.choose_spec.choose_spec.choose_spec.1.1
  obtain ⟨O', _, _, _, _, j, Ω, _, i, g, hj, hgi, hsq, hq⟩ := exists_points_extension f hf x.P.A.hom
    (fun p : A => p.1.left ≫ φ) (fun p => by
      rw [Category.assoc, hp.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
  obtain ⟨x', hx'⟩ := KeyPow.keyIn_baseChange laws.polBaseChange O O' x j
  obtain ⟨φ', w', H'⟩ := (KeyVia.main _ _ x x' j).1.1 hx'
  have hg' : x'.P.g = x.P.g := H'.choose_spec.choose
  have hp' : IsPullback φ' x'.P.A.hom x.P.A.hom (spMap j) := H'.choose_spec.choose_spec.choose_spec.1.1
  choose s' hs' using fun i : Fin x'.P.g => (((KeyVia.main _ _ x x' j).2 φ' w' H').1 n (s (i.cast hg'))).exists
  obtain ⟨y, hy⟩ := KeyPow.keyIn_baseChange laws.polBaseChange F Ω xF i
  obtain ⟨ψ, v, H₁⟩ := (KeyVia.main _ _ xF y i).1.1 hy
  have hg₁ : y.P.g = xF.P.g := H₁.choose_spec.choose
  choose s₁ hs₁ using fun a : Fin y.P.g => (((KeyVia.main _ _ xF y i).2 ψ v H₁).1 n (sF (a.cast hg₁))).exists
  obtain ⟨v₂, H₂, sec₂⟩ := keyVia_trans hx H₁
  obtain ⟨χ, v₃, H₃, hχ, sec₃⟩ := KaLift.keyVia_cancel (f' := g) H' (hsq.symm ▸ H₂)
  have hg₃ : y.P.g = x'.P.g := (hg₁.trans hg).trans hg'.symm
  obtain ⟨u₁, hu₁, hu₁'⟩ := exists_pull_hom H₁ i.injective
  obtain ⟨u₃, hu₃, hu₃'⟩ := exists_pull_hom H₃ hgi
  have hA : ∀ p ∈ A, ∃ q, u₃ q = u₁ p := fun p hpA => by
    obtain ⟨q, e₁, e₂⟩ := hq ⟨p, hpA⟩
    have hw : q ≫ x.P.A.hom = 𝟙 _ ≫ spMap j := e₁.trans (Category.id_comp _).symm
    let q' : Pt x' := Over.homMk (hp'.lift q (𝟙 _) hw) (hp'.lift_snd _ _ _)
    have e₃ : q'.left ≫ φ' = q := hp'.lift_fst _ _ _
    have e₄ : q'.left ≫ x'.P.A.hom = 𝟙 _ := Over.w _
    have e₅ : (u₁ p).left ≫ y.P.A.hom = 𝟙 _ := Over.w _
    have hp₃ : IsPullback χ y.P.A.hom x'.P.A.hom (spMap g) := H₃.choose_spec.choose_spec.choose_spec.1.1
    refine ⟨q', ((hu₃' q' _).2 (hp'.hom_ext ?_ ?_)).symm⟩
    · rw [Category.assoc, Category.assoc, hχ, e₃, e₂, ← Category.assoc, (hu₁' p _).1 rfl, Category.assoc]
    · rw [Category.assoc, Category.assoc, e₄, hp₃.w, ← Category.assoc, e₅]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  choose z' hz' using fun a => hA (z a) (Or.inl ⟨a, rfl⟩)
  obtain ⟨ch₁, E₁⟩ := etZ_pull hg₁ H₁ hs₁ (z' := fun a => u₁ (z a)) (fun a => (hu₁' _ _).1 rfl) E
  have hO : ∀ m : ℕ, 1 ≤ m → IsUnit (m : O') := fun m hm => by
    have := (isUnit_iff_ne_zero.2 (by exact_mod_cast (by omega : m ≠ 0) : (m : ℚ) ≠ 0)).map (j.comp (algebraMap ℚ O))
    rwa [map_natCast] at this
  haveI : CharZero Ω := (RingHom.charZero_iff ((i.comp f).comp (algebraMap ℚ O)).injective).1 inferInstance
  obtain ⟨u, hu⟩ : ∃ u : O'ˣ, KaVal y n l l' al s₁ (Units.map g.toMonoidHom u) := by
    refine exists_unit_kaVal laws hg₃ (s := s') (s' := s₁) (by rw [hg₁]) z' hO hgi (hg'.symm ▸ hadm) H₃
      (fun a => sec₃ n _ _ _ (hs' (a.cast hg₃)) (sec₂ n _ _ _ (hs (a.cast hg₁)) (hs₁ a))) ?_ E₁
      (fun a => (hu₃' _ _).1 (hz' a).symm) ?_
    · have hcl : IsClosed {t : x.P.A.left | x.P.A.hom t = IsLocalRing.closedPoint O ∧ ∀ a, t ∉ Out.nonzeroLocus (s a)} := by
        refine IsClosed.inter ((IsLocalRing.isClosed_singleton_closedPoint O).preimage x.P.A.hom.continuous) ?_
        change IsClosed {t : x.P.A.left | ∀ a, t ∉ Out.nonzeroLocus (s a)}
        rw [Set.setOf_forall]
        exact isClosed_iInter fun a => (Out.nonzeroLocus (s a)).isOpen.isClosed_compl
      refine (finite_preimage_fibre hp' hcl hfin (IsLocalRing.closedPoint O')).subset fun t ht => ⟨ht.1, ?_, fun a h => ?_⟩
      · exact (congrArg (fun q => q t) hp'.w).trans ((congrArg (spMap j) ht.1).trans (IsLocalRing.comap_closedPoint j))
      · exact ht.2 (a.cast hg'.symm) (EtBaseChange.mem_nonzeroLocus_via (hs' (a.cast hg'.symm)) t h)
    · intro k hk c hc
      rw [hg'.trans hg.symm] at hc ⊢
      obtain ⟨ξ, h₁, h₂, h₃⟩ := hS' k c hk hc
      choose ξ' hξ' using fun I r => hA (ξ I r) (Or.inr (Set.mem_biUnion hc (by
        rcases hk with rfl | rfl
        exacts [Or.inl (h₁ I r), Or.inr (h₁ I r)])))
      refine ⟨ξ', fun I I' h => h₂ (funext fun r => hu₁ ?_), fun I r => hu₃ ?_⟩
      · rw [← hξ', ← hξ', h]
      · have := congrArg u₁ (h₃ I r)
        simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_zpow, map_one, hξ'] at this ⊢
        exact this
  have h₁ := T.keyInvariant_baseChange laws F Ω xF y i ψ v n l l' al hg₁ sF s₁ κ (hg.symm ▸ hadm) H₁ hs₁ hκ
  have h₂ : i κ = g u := congrArg Units.val
    (T.keyInvariantFromIntersection_unique laws Ω y n l l' al s₁ _ _ ((hg₁.trans hg).symm ▸ hadm) h₁ hu)
  have h₃ : g (j a) = g (u ^ e : O'ˣ) := by
    refine (RingHom.congr_fun hsq a).trans ?_
    rw [RingHom.comp_apply, ← ha, map_zpow₀, h₂]
    exact ((congrArg Units.val (map_zpow (Units.map g.toMonoidHom) u e)).trans (Units.val_zpow_eq_zpow_val _ _)).symm
  exact (isUnit_map_iff j a).1 (hgi h₃ ▸ Units.isUnit _)

end GlobalTheory.KaFiniteUnit
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  atlas_forward_decl GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros
end

section
set_option autoImplicit false

section

open Polynomial TensorProduct

namespace GlobalTheory.KeyLine

theorem exists_common_field {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L₁ ⊗[F] L₂)
  letI := Ideal.Quotient.field m
  refine ⟨L₁ ⊗[F] L₂ ⧸ m, inferInstance, (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem mem_range_of_forall_eq {F E : Type} [Field F] [CharZero F] [Field E] (i : F →+* E) (κ : E)
    (h : ∀ (L : Type) [Field L] (g₁ g₂ : E →+* L), g₁.comp i = g₂.comp i → g₁ κ = g₂ κ) : ∃ c, i c = κ := by
  letI := i.toAlgebra
  let D : IntermediateField F E := IntermediateField.adjoin F {κ}
  have key : ∀ (L : Type) [Field L] [Algebra F L] (f₁ f₂ : D →ₐ[F] L), f₁ = f₂ := by
    intro L _ _ f₁ f₂
    obtain ⟨L₁, _, i₁, g₁, e₁⟩ := exists_common_field f₁.toRingHom D.val.toRingHom
    obtain ⟨L₂, _, i₂, g₂, e₂⟩ := exists_common_field f₂.toRingHom D.val.toRingHom
    obtain ⟨L₃, _, j₁, j₂, e₃⟩ := exists_common_field i₁ i₂
    have a₁ : ∀ d : D, i₁ (f₁ d) = g₁ d := fun d => RingHom.congr_fun e₁ d
    have a₂ : ∀ d : D, i₂ (f₂ d) = g₂ d := fun d => RingHom.congr_fun e₂ d
    have a₃ : ∀ d : L, j₁ (i₁ d) = j₂ (i₂ d) := fun d => RingHom.congr_fun e₃ d
    have e : j₁ (g₁ κ) = j₂ (g₂ κ) := h L₃ (j₁.comp g₁) (j₂.comp g₂) (RingHom.ext fun c => by
      have b₁ := a₁ (algebraMap F D c)
      have b₂ := a₂ (algebraMap F D c)
      rw [AlgHom.commutes] at b₁ b₂
      exact (congrArg j₁ b₁.symm).trans ((a₃ _).trans (congrArg j₂ b₂)))
    refine IntermediateField.algHom_ext_of_eq_adjoin F (S := D) rfl fun y hy => ?_
    obtain rfl : y = κ := hy
    refine i₁.injective (j₁.injective ?_)
    exact (congrArg j₁ (a₁ ⟨y, IntermediateField.mem_adjoin_simple_self F y⟩)).trans (e.trans
      ((congrArg j₂ (a₂ ⟨y, IntermediateField.mem_adjoin_simple_self F y⟩)).symm.trans (a₃ _).symm))
  have key' : ∀ (L : Type) [Field L] (f₁ f₂ : D →+* L),
      f₁.comp (algebraMap F D) = f₂.comp (algebraMap F D) → f₁ = f₂ := by
    intro L _ f₁ f₂ hf
    letI := (f₁.comp (algebraMap F D)).toAlgebra
    exact congrArg AlgHom.toRingHom (key L ⟨f₁, fun _ => rfl⟩ ⟨f₂, fun c => (RingHom.congr_fun hf c).symm⟩)
  haveI : IsPurelyInseparable F D := by
    haveI : Nonempty (D →+* AlgebraicClosure E) := ⟨(algebraMap E _).comp D.val.toRingHom⟩
    refine IsPurelyInseparable.of_injective_comp_algebraMap F D (AlgebraicClosure E) fun f₁ f₂ hf => ?_
    exact key' _ f₁ f₂ hf
  obtain ⟨c, hc⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F D
    ⟨κ, IntermediateField.mem_adjoin_simple_self F κ⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_lift_fraction {A E : Type} (F : Type) [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Field E]
    (g : A →+* E) (hg : Function.Injective g) : ∃ i : F →+* E, i.comp (algebraMap A F) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun p => IsFractionRing.lift_algebraMap hg p⟩

theorem exists_field_extend {K O : Type} [Field K] [CommRing O] [IsDomain O] (ψ : K[X] →+* O)
    (hψ : Function.Injective ψ) : ∃ (E : Type) (_ : Field E) (ι : O →+* E) (i : RatFunc K →+* E),
      Function.Injective ι ∧ i.comp (algebraMap K[X] (RatFunc K)) = ι.comp ψ := by
  obtain ⟨E, _, ι, hι⟩ : ∃ (E : Type) (_ : Field E) (ι : O →+* E), Function.Injective ι :=
    ⟨FractionRing O, inferInstance, algebraMap _ _, IsFractionRing.injective O (FractionRing O)⟩
  obtain ⟨i, hi⟩ := exists_lift_fraction (RatFunc K) (ι.comp ψ) (hι.comp hψ)
  exact ⟨E, inferInstance, ι, i, hι, hi⟩

theorem exists_localRing (K : Type) [Field K] (a : K) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (ψ : K[X] →+* O) (r : O →+* K)
      (g : O →+* RatFunc K), r.comp ψ = evalRingHom a ∧ RingHom.ker r = IsLocalRing.maximalIdeal O ∧
      g.comp ψ = algebraMap K[X] (RatFunc K) ∧ Function.Injective g := by
  let P : Ideal K[X] := RingHom.ker (evalRingHom a)
  haveI hP : P.IsPrime := RingHom.ker_isPrime _
  have h0 : P ≠ ⊥ := fun h => by
    have : X - C a ∈ P := by simp [P, RingHom.mem_ker]
    rw [h] at this
    exact X_sub_C_ne_zero a this
  let O := Localization.AtPrime P
  haveI : IsDomain O := IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] h0 O
  have hr : ∀ y : P.primeCompl, IsUnit (evalRingHom a y) := fun y => Ne.isUnit y.2
  have hg : ∀ y : P.primeCompl, IsUnit (algebraMap K[X] (RatFunc K) y) := fun y =>
    Ne.isUnit fun h => y.2 (by
      rw [(map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).1 h]; exact P.zero_mem)
  have hs : Function.Surjective (IsLocalization.lift (S := O) hr) := fun k =>
    ⟨algebraMap K[X] O (C k), by rw [IsLocalization.lift_eq]; simp⟩
  refine ⟨O, inferInstance, inferInstance, inferInstance, algebraMap K[X] O, IsLocalization.lift hr, IsLocalization.lift hg,
    IsLocalization.lift_comp hr, IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs),
    IsLocalization.lift_comp hg, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro p q
  rw [(IsFractionRing.injective K[X] (RatFunc K)).eq_iff,
    (IsLocalization.injective O P.primeCompl_le_nonZeroDivisors).eq_iff]

theorem exists_eq_C {K : Type} [Field K] [IsAlgClosed K] (c : RatFunc K) (hc : c ≠ 0)
    (h : ∀ (a : K) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K)
      (g : O →+* RatFunc K), r.comp ψ = evalRingHom a → RingHom.ker r = IsLocalRing.maximalIdeal O →
      g.comp ψ = algebraMap K[X] (RatFunc K) → Function.Injective g → ∀ (u : O) (e : ℤ), e ≠ 0 → c ^ e = g u → IsUnit u) :
    ∃ k : K, c = algebraMap K[X] (RatFunc K) (C k) := by
  have hq := c.denom_ne_zero
  have hp := RatFunc.num_ne_zero hc
  have key : ∀ (a : K) (p q : K[X]) (e : ℤ), e ≠ 0 → q.eval a ≠ 0 →
      c ^ e = algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q → p.eval a ≠ 0 := by
    intro a p q e he hqa hce
    obtain ⟨O, _, _, _, ψ, r, g, hr, hk, hg, hi⟩ := exists_localRing K a
    have hr' : ∀ p, r (ψ p) = p.eval a := fun p => RingHom.congr_fun hr p
    have hg' : ∀ p, g (ψ p) = algebraMap K[X] (RatFunc K) p := fun p => RingHom.congr_fun hg p
    have hu : IsUnit (ψ q) := by
      by_contra hn
      have : ψ q ∈ RingHom.ker r := hk ▸ hn
      exact hqa ((hr' q).symm.trans this)
    obtain ⟨v, hv⟩ := hu
    have := h a O ψ r g hr hk hg hi (ψ p * v⁻¹.val) e he (by
      rw [hce, map_mul, map_units_inv, hv, hg', hg', div_eq_mul_inv])
    have := (isUnit_of_mul_isUnit_left this).map r
    rw [hr'] at this
    exact this.ne_zero
  have hboth : ∀ a : K, c.num.eval a ≠ 0 ∧ c.denom.eval a ≠ 0 := by
    intro a
    have h₁ := key a c.num c.denom 1 one_ne_zero
    have h₂ := key a c.denom c.num (-1) (by norm_num)
    rw [zpow_one, c.num_div_denom] at h₁
    rw [zpow_neg_one, ← inv_div, c.num_div_denom] at h₂
    obtain ⟨u, v, huv⟩ := c.isCoprime_num_denom
    have e := congrArg (eval a) huv
    rw [eval_add, eval_mul, eval_mul, eval_one] at e
    by_cases hd : c.denom.eval a = 0
    · have hn : c.num.eval a ≠ 0 := fun hn => by simp [hn, hd] at e
      exact absurd hd (h₂ hn rfl)
    · exact ⟨h₁ hd rfl, hd⟩
  have hconst : ∀ p : K[X], (∀ a, p.eval a ≠ 0) → ∃ k, p = C k := fun p hp => by
    by_cases hd : p.degree = 0
    · exact ⟨_, eq_C_of_degree_eq_zero hd⟩
    · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hd
      exact absurd ha (hp a)
  obtain ⟨k, hk⟩ := hconst _ fun a => (hboth a).1
  obtain ⟨k', hk'⟩ := hconst _ fun a => (hboth a).2
  refine ⟨k / k', ?_⟩
  rw [← c.num_div_denom, hk, hk', RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀]

theorem eq_of_line {K : Type} [Field K] [CharZero K] [IsAlgClosed K]
    (V : ∀ (R : Type) [CommRing R], (K[X] →+* R) → Rˣ → Prop)
    (hmap : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      (ψ : K[X] →+* R) (g : R →+* R') (κ : Rˣ), V R ψ κ → V R' (g.comp ψ) (Units.map g.toMonoidHom κ))
    (huniq : ∀ (L : Type) [Field L] (ψ : K[X] →+* L) (κ κ' : Lˣ), V L ψ κ → V L ψ κ' → κ = κ')
    (hlift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K) (κ : Kˣ),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V K (r.comp ψ) κ →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (j : O →+* O') (r' : O' →+* K)
        (u : O'ˣ), Function.Injective j ∧ r'.comp j = r ∧ V O' (j.comp ψ) u)
    (hunit : ∀ (a : K) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ψ : K[X] →+* O) (r : O →+* K)
      (L : Type) [Field L] (g : O →+* L) (κ : Lˣ) (u : O) (e : ℤ), r.comp ψ = evalRingHom a →
      RingHom.ker r = IsLocalRing.maximalIdeal O → Function.Injective g → V L (g.comp ψ) κ → (κ : L) ^ e = g u →
      e ≠ 0 → IsUnit u)
    {a₀ a₁ : K} {κ₀ κ₁ : Kˣ} (h₀ : V K (evalRingHom a₀) κ₀) (h₁ : V K (evalRingHom a₁) κ₁) : κ₀ = κ₁ := by
  let χ : K[X] →+* RatFunc K := algebraMap _ _
  have hχ : Function.Injective χ := IsFractionRing.injective _ _
  haveI : CharZero (RatFunc K) := (RingHom.charZero_iff (χ.comp C).injective).1 inferInstance

  have gen : ∀ (a : K) (κ : Kˣ), V K (evalRingHom a) κ → ∃ (E : Type) (_ : Field E) (i : RatFunc K →+* E) (μ : Eˣ),
      V E (i.comp χ) μ ∧ ∀ k : K, (μ : E) = i (χ (C k)) → (κ : K) = k := by
    intro a κ hκ
    obtain ⟨O, _, _, _, ψ, r, g, hr, hk, hg, hi⟩ := exists_localRing K a
    obtain ⟨O', _, _, _, j, r', u, hj, hr', hu⟩ := hlift O ψ r κ hk (hr ▸ hκ)
    have hψ : Function.Injective ψ := Function.Injective.of_comp (f := g) (by
      rw [← RingHom.coe_comp, hg]; exact hχ)
    obtain ⟨E, _, ι, i, hι, hi'⟩ := exists_field_extend (j.comp ψ) (hj.comp hψ)
    refine ⟨E, inferInstance, i, Units.map ι.toMonoidHom u, ?_, fun k hk => ?_⟩
    · rw [show i.comp χ = _ from hi']
      exact hmap _ _ _ ι u hu
    · have e : (u : O') = j (ψ (C k)) := hι ((show ι u = i (χ (C k)) from hk).trans (RingHom.congr_fun hi' (C k)))
      have h' := hmap _ _ _ r' u hu
      rw [← RingHom.comp_assoc, hr', hr] at h'
      rw [huniq K _ _ _ hκ h']
      change r' u = k
      rw [e]
      exact (RingHom.congr_fun hr' _).trans ((RingHom.congr_fun hr _).trans eval_C)
  obtain ⟨E₀, _, i₀, μ₀, v₀, e₀⟩ := gen a₀ κ₀ h₀
  obtain ⟨E₁, _, i₁, μ₁, v₁, e₁⟩ := gen a₁ κ₁ h₁
  obtain ⟨c, hc⟩ := mem_range_of_forall_eq i₀ μ₀ fun L _ g₁ g₂ hg => by
    have b₁ := hmap _ _ _ g₁ μ₀ v₀
    have b₂ := hmap _ _ _ g₂ μ₀ v₀
    rw [← RingHom.comp_assoc] at b₁ b₂
    rw [hg] at b₁
    exact congrArg Units.val (huniq L _ _ _ b₁ b₂)
  obtain ⟨k, rfl⟩ := exists_eq_C c (fun h => μ₀.ne_zero (by rw [← hc, h, map_zero]))
    fun a O _ _ _ ψ r g hr hk hg hi u e he hu => hunit a O ψ r E₀ (i₀.comp g) μ₀ u e hr hk (i₀.injective.comp hi)
      (by rw [RingHom.comp_assoc, hg]; exact v₀) (by rw [← hc, ← map_zpow₀, hu]; rfl) he
  obtain ⟨L, _, j₀, j₁, hj⟩ := exists_common_field i₀ i₁
  have b₀ := hmap _ _ _ j₀ μ₀ v₀
  have b₁ := hmap _ _ _ j₁ μ₁ v₁
  rw [← RingHom.comp_assoc] at b₀ b₁
  rw [hj] at b₀
  have e : j₀ μ₀ = j₁ μ₁ := congrArg Units.val (huniq L _ _ _ b₀ b₁)
  refine Units.ext ((e₀ k hc.symm).trans (e₁ k (j₁.injective ?_)).symm)
  rw [← e, ← hc]
  exact RingHom.congr_fun hj _

end GlobalTheory.KeyLine

end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyLine

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {n : ℕ}

def lineFn {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (τ : R) (a b : ∀ i, Γ(X, L.U i)) : ∀ i, Γ(X, L.U i) :=
  fun i => AbLaw.cst p _ (1 - τ) * a i + AbLaw.cst p _ τ * b i

theorem via_lineFn {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a) (hb : KeyVia.Via w l b' b) (τ : R) :
    KeyVia.Via w l (lineFn p' (f τ) a' b') (lineFn p τ a b) := by
  intro j i h
  simp only [lineFn]
  rw [map_add, map_mul, map_mul, ha j i h, hb j i h, KeyVia.appLE_cst f p p' hφ, KeyVia.appLE_cst f p p' hφ, map_add,
    map_mul, map_mul, rs_cst, rs_cst, map_sub f, map_one f]
  exact (congrArg₂ (· + ·) (mul_left_comm _ _ _) (mul_left_comm _ _ _)).trans (mul_add _ _ _).symm

theorem exists_lineSec {X : Scheme.{0}} {M : LB X} (p : X ⟶ Sp R) (τ : R) (a b : M.Sec) :
    ∃ s : M.Sec, s.f = lineFn p τ a.f b.f := by
  refine ⟨⟨lineFn p τ a.f b.f, fun i j => ?_⟩, rfl⟩
  have ha := a.compat i j
  have hb := b.compat i j
  simp only [lineFn]
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, ha, hb, rs_cst, rs_cst, rs_cst, rs_cst]
  ring

def OnLine (y : KeyIn R) (τ : R) (a b s : RR y n) : Prop :=
  s.f = lineFn (L := y.P.L) y.P.A.hom τ a.f b.f

theorem exists_onLine (y : KeyIn R) (τ : R) (a b : RR y n) : ∃ s, OnLine y τ a b s :=
  exists_lineSec (M := AbLaw.pw y.P.L (n : ℤ)) y.P.A.hom τ a b

theorem secVia_iff_onLine {y : KeyIn R} {y' : KeyIn R'} {g : R →+* R'} {φ w} (H : KeyVia y' y g φ w) {τ : R}
    {a b s : RR y n} {a' b' s' : RR y' n} (ha : SecVia y' y φ w a' a) (hb : SecVia y' y φ w b' b)
    (hs : OnLine y τ a b s) : SecVia y' y φ w s' s ↔ OnLine y' (g τ) a' b' s' := by
  have e := via_lineFn (L := y.P.L) (L' := y'.P.L) (w := w) (l := n) (a := a.f) (b := b.f) (a' := a'.f) (b' := b'.f)
    g y.P.A.hom y'.P.A.hom (keyVia_isPullback H).w ha hb τ
  have e' : KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n (lineFn (L := y'.P.L) y'.P.A.hom (g τ) a'.f b'.f) s.f :=
    (congrArg (KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n _) hs).mpr e
  constructor
  · intro h
    exact KeyVia.Via.unique (L := y.P.L) (L' := y'.P.L) (w := w) (l := n) (a := s.f) (a' := s'.f) y.P.isLB h e'
  · intro h
    exact (congrArg (fun q => KeyVia.Via (L := y.P.L) (L' := y'.P.L) w n q s.f) h).mpr e'

theorem lineFn_zero {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (a b : ∀ i, Γ(X, L.U i)) : a = lineFn p 0 a b := by
  funext i
  simp only [lineFn, sub_zero, map_one, map_zero, _root_.one_mul, zero_mul, add_zero]

theorem lineFn_one {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp R) (a b : ∀ i, Γ(X, L.U i)) : b = lineFn p 1 a b := by
  funext i
  simp only [lineFn, sub_self, map_one, map_zero, _root_.one_mul, zero_mul, zero_add]

theorem onLine_zero (y : KeyIn R) (a b : RR y n) : OnLine y 0 a b a := lineFn_zero (L := y.P.L) _ a.f b.f

theorem onLine_one (y : KeyIn R) (a b : RR y n) : OnLine y 1 a b b := lineFn_one (L := y.P.L) _ a.f b.f

theorem mem_nonzeroLocus_of_via {y : KeyIn R} {y' : KeyIn R'} {φ w} {s' : RR y' n} {s : RR y n}
    (hs : SecVia y' y φ w s' s) (z : y'.P.A.left) (hz : z ∈ Out.nonzeroLocus s') : φ z ∈ Out.nonzeroLocus s := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k, hk⟩ := exists_chart y.P.isLB (φ z)
  have hle : (y.P.L.pull φ).U (fun _ => k) ⊓ y'.P.L.U i ≤ φ ⁻¹ᵁ y.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have hm : z ∈ (y.P.L.pull φ).U (fun _ => k) ⊓ y'.P.L.U i := ⟨mem_pull.2 hk, y'.P.A.left.basicOpen_le _ hi⟩
  have h1 : z ∈ y'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    refine (congrArg y'.P.A.left.basicOpen e).ge ((Scheme.basicOpen_mul _ _ _).ge ⟨?_, ?_⟩)
    · exact (Scheme.basicOpen_of_isUnit _ ((Units.isUnit (w.s (fun _ => k, i))).pow n)).ge hm
    · exact (Scheme.basicOpen_res _ _ _).ge ⟨hm, hi⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_appLE φ _ (y.P.L.U k) hle (s.f k)).le h1).2⟩

variable {x : KeyIn K} (s₀ s₁ : Fin x.P.g → RR x n)

def IsLinePt (f : K →+* R) (τ : R) (y : KeyIn R) (s : Fin y.P.g → RR y n) : Prop :=
  ∃ φ w, ∃ hg : y.P.g = x.P.g, KeyVia y x f φ w ∧ ∀ i, ∃ a b, SecVia y x φ w a (s₀ (i.cast hg)) ∧
    SecVia y x φ w b (s₁ (i.cast hg)) ∧ OnLine y τ a b (s i)

theorem exists_isLinePt (f : K →+* R) (τ : R) : ∃ y s, IsLinePt s₀ s₁ f τ y s := by
  obtain ⟨y, hy⟩ := KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, H⟩ := (KeyVia.main _ _ x y f).1.1 hy
  have hp := ((KeyVia.main _ _ x y f).2 φ w H).1 n
  choose a ha using fun i : Fin y.P.g => (hp (s₀ (i.cast (keyVia_g H)))).exists
  choose b hb using fun i : Fin y.P.g => (hp (s₁ (i.cast (keyVia_g H)))).exists
  choose s hs using fun i => exists_onLine y τ (a i) (b i)
  exact ⟨y, s, φ, w, keyVia_g H, H, fun i => ⟨a i, b i, ha i, hb i, hs i⟩⟩

variable {s₀ s₁} {f : K →+* R} {τ : R} {y : KeyIn R} {s : Fin y.P.g → RR y n} {g : R →+* R'} {y' : KeyIn R'}
  {s' : Fin y'.P.g → RR y' n}

theorem IsLinePt.g_eq (h : IsLinePt s₀ s₁ f τ y s) : y.P.g = x.P.g := by
  obtain ⟨_, _, hg, _⟩ := h
  exact hg

theorem IsLinePt.cancel (h : IsLinePt s₀ s₁ f τ y s) (h' : IsLinePt s₀ s₁ (g.comp f) (g τ) y' s') :
    ∃ φ w, ∃ hg : y'.P.g = y.P.g, KeyVia y' y g φ w ∧ ∀ i, SecVia y' y φ w (s' i) (s (i.cast hg)) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  obtain ⟨φ'', w'', hg'', H'', hs''⟩ := h'
  obtain ⟨φ', w', H', -, hv⟩ := keyVia_cancel H H''
  refine ⟨φ', w', hg''.trans hg.symm, H', fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs (i.cast (hg''.trans hg.symm))
  obtain ⟨a', b', ha', hb', hl'⟩ := hs'' i
  exact (secVia_iff_onLine H' (hv _ _ _ _ ha ha') (hv _ _ _ _ hb hb') hl).2 hl'

theorem IsLinePt.trans (h : IsLinePt s₀ s₁ f τ y s) {φ' w'} (hg' : y'.P.g = y.P.g) (H' : KeyVia y' y g φ' w')
    (hs' : ∀ i, SecVia y' y φ' w' (s' i) (s (i.cast hg'))) : IsLinePt s₀ s₁ (g.comp f) (g τ) y' s' := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  obtain ⟨w'', H'', hv⟩ := keyVia_trans H H'
  refine ⟨φ' ≫ φ, w'', hg'.trans hg, H'', fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs (i.cast hg')
  obtain ⟨a', ha'⟩ := (((KeyVia.main _ _ y y' g).2 φ' w' H').1 n a).exists
  obtain ⟨b', hb'⟩ := (((KeyVia.main _ _ y y' g).2 φ' w' H').1 n b).exists
  exact ⟨a', b', hv _ _ _ _ ha ha', hv _ _ _ _ hb hb', (secVia_iff_onLine H' ha' hb' hl).1 (hs' i)⟩

theorem IsLinePt.via {t : K} (h : IsLinePt s₀ s₁ f (f t) y s) {r : Fin x.P.g → RR x n}
    (hr : ∀ i, OnLine x t (s₀ i) (s₁ i) (r i)) :
    ∃ φ w, ∃ hg : y.P.g = x.P.g, KeyVia y x f φ w ∧ ∀ i, SecVia y x φ w (s i) (r (i.cast hg)) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h
  refine ⟨φ, w, hg, H, fun i => ?_⟩
  obtain ⟨a, b, ha, hb, hl⟩ := hs i
  exact (secVia_iff_onLine H ha hb (hr _)).2 hl

theorem finZ_of_via_id {z : KeyIn K} {φ w} (hg : z.P.g = x.P.g) (H : KeyVia z x (RingHom.id K) φ w)
    {r : Fin x.P.g → RR x n} {r' : Fin z.P.g → RR z n} (hs : ∀ i, SecVia z x φ w (r' i) (r (i.cast hg)))
    (h : FinZ x r) : FinZ z r' := by
  have hp := keyVia_isPullback H
  haveI : IsIso (spMap (RingHom.id K)) := by
    have : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
    rw [this]
    infer_instance
  haveI : IsIso φ := hp.isIso_fst_of_isIso
  refine Set.Finite.of_finite_image (f := φ) (h.subset ?_) φ.homeomorph.injective.injOn
  rintro _ ⟨p, hp, rfl⟩ i hi
  exact hp (i.cast hg.symm) (EtBaseChange.mem_nonzeroLocus_via (hs _) p hi)

theorem finite_closedFibre {O k : Type} [CommRing O] [IsLocalRing O] [Field k] {r : O →+* k}
    (hr : RingHom.ker r = IsLocalRing.maximalIdeal O) {z : KeyIn O} {zk : KeyIn k} {φ w} (hg : zk.P.g = z.P.g)
    (H : KeyVia zk z r φ w) {t : Fin z.P.g → RR z n} {tk : Fin zk.P.g → RR zk n}
    (hs : ∀ i, SecVia zk z φ w (tk i) (t (i.cast hg))) (h : FinZ zk tk) :
    {p : z.P.A.left | z.P.A.hom p = IsLocalRing.closedPoint O ∧ ∀ i, p ∉ Out.nonzeroLocus (t i)}.Finite := by
  refine (h.image φ).subset ?_
  rintro p ⟨hp, hz⟩
  have e : spMap r (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    change Ideal.comap r (IsLocalRing.maximalIdeal k) = IsLocalRing.maximalIdeal O
    rw [IsLocalRing.maximalIdeal_eq_bot, ← hr, RingHom.ker_eq_comap_bot]
  obtain ⟨q, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (keyVia_isPullback H) p (IsLocalRing.closedPoint k)
    (hp.trans e.symm)
  exact ⟨q, fun i hi => hz _ (mem_nonzeroLocus_of_via (hs i) q hi), rfl⟩

open Polynomial in

theorem kaVal_eq_of_line : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x' : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s₀ s₁ : Fin x'.P.g → RR x' n) (κ₀ κ₁ : Kˣ), admitted x'.P.g n l l' al → (∀ (t : K) (s : Fin x'.P.g → RR x' n), (∀ i c, (show Γ(x'.P.A.left, x'.P.L.U c) from (s i).f c) = AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from (s₀ i).f c) + AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from (s₁ i).f c)) → FinZ x' s) → KaVal x' n l l' al s₀ κ₀ → KaVal x' n l l' al s₁ κ₁ → κ₀ = κ₁ := by
  intro hL K _ _ _ x n l l' al s₀ s₁ κ₀ κ₁ hA hfin h₀ h₁
  let V : ∀ (R : Type) [CommRing R], (K[X] →+* R) → Rˣ → Prop := fun R _ ψ κ =>
    ∃ y s, IsLinePt s₀ s₁ (ψ.comp C) (ψ X) y s ∧ KaVal y n l l' al s κ
  have adm : ∀ {R : Type} [CommRing R] {f : K →+* R} {τ : R} {y : KeyIn R} {s : Fin y.P.g → RR y n},
      IsLinePt s₀ s₁ f τ y s → admitted y.P.g n l l' al := fun h => by rw [h.g_eq]; exact hA
  have hev : ∀ a : K, (evalRingHom a).comp C = RingHom.id K := fun a => RingHom.ext fun _ => eval_C
  have hpt : ∀ (a : K) (r : Fin x.P.g → RR x n) (κ : Kˣ), (∀ i, OnLine x a (s₀ i) (s₁ i) (r i)) →
      KaVal x n l l' al r κ → V K (evalRingHom a) κ := by
    intro a r κ hr hκ
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (RingHom.id K) a
    obtain ⟨φ, w, hg, H, hs⟩ := IsLinePt.via (t := a) hy hr
    refine ⟨y, s, ?_, GlobalTheory.T.keyInvariant_baseChange hL K K x y _ φ w n l l' al hg r s κ hA H hs hκ⟩
    rw [hev, show evalRingHom a X = a from eval_X]
    exact hy
  refine eq_of_line V ?_ ?_ ?_ ?_ (hpt 0 s₀ κ₀ (fun i => onLine_zero x _ _) h₀)
    (hpt 1 s₁ κ₁ (fun i => onLine_one x _ _) h₁)
  · rintro R R' _ _ _ _ _ ψ g κ ⟨y, s, hy, hκ⟩
    obtain ⟨y', s', hy'⟩ := exists_isLinePt s₀ s₁ (g.comp (ψ.comp C)) (g (ψ X))
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel hy'
    exact ⟨y', s', hy', GlobalTheory.T.keyInvariant_baseChange hL R R' y y' g φ w n l l' al hg s s' κ (adm hy) H hs hκ⟩
  · rintro L _ ψ κ κ' ⟨y, s, hy, hκ⟩ ⟨y', s', hy', hκ'⟩
    haveI : CharZero L := (RingHom.charZero_iff (ψ.comp C).injective).1 inferInstance
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := RingHom.id L) hy'
    exact GlobalTheory.T.keyInvariantFromIntersection_unique hL L y' n l l' al s' _ _ (adm hy')
      (GlobalTheory.T.keyInvariant_baseChange hL L L y y' _ φ w n l l' al hg s s' κ (adm hy) H hs hκ) hκ'
  · rintro O _ _ _ ψ r κ hr ⟨yk, sk, hyk, zk, chk, -, -, -, -, -, -, -, hE, -⟩
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (ψ.comp C) (ψ X)
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := r) hyk
    have hu : IsUnit ((degProd y.P.g n l l' : ℕ) : O) := by
      obtain ⟨-, h₂, h₃, -⟩ := adm hy
      have hne : degProd y.P.g n l l' ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => by
        have : j * n ≤ y.P.g * n := Nat.mul_le_mul_right n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
        exact Nat.mul_ne_zero (by omega) (by omega)
      have := (Ne.isUnit (Nat.cast_ne_zero.2 hne : ((degProd y.P.g n l l' : ℕ) : K) ≠ 0)).map (ψ.comp C)
      rwa [map_natCast] at this
    obtain ⟨O', _, _, _, j, r', y', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩ :=
      GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O K r y yk φ w n l l' al _ hg s sk zk chk hr (adm hy) hu H hs hE
    exact ⟨O', inferInstance, inferInstance, inferInstance, j, r', u, hj, hr', y', s', hy.trans hg' H' hs', hu'⟩
  · rintro a O _ _ _ ψ r L _ g κ u e hψ hr hgi ⟨yL, sL, hyL, hκ⟩ hu he
    letI : Algebra ℚ O := ((ψ.comp C).comp (algebraMap ℚ K)).toAlgebra
    obtain ⟨y, s, hy⟩ := exists_isLinePt s₀ s₁ (ψ.comp C) (ψ X)
    obtain ⟨φ, w, hg, H, hs⟩ := hy.cancel (g := g) hyL
    obtain ⟨yk, sk, hyk⟩ := exists_isLinePt s₀ s₁ (RingHom.id K) a
    choose t ht using fun i => exists_onLine x a (s₀ i) (s₁ i)
    obtain ⟨φ₀, w₀, hg₀, H₀, hs₀⟩ := IsLinePt.via (t := a) hyk ht
    have hk := finZ_of_via_id hg₀ H₀ hs₀ (hfin a t fun i c => congrFun (ht i) c)
    obtain ⟨φ₁, w₁, hg₁, H₁, hs₁⟩ := hy.cancel (g := r) (y' := yk) (s' := sk) (by
      rw [← RingHom.comp_assoc, hψ, hev, show r (ψ X) = a from (RingHom.congr_fun hψ X).trans eval_X]
      exact hyk)
    exact GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros hL O L g y yL φ w n l l' al hg s sL κ u e hgi (adm hy) H hs
      (finite_closedFibre hr hg₁ H₁ hs₁ hk) hκ hu he

end GlobalTheory.KeyLine
end
end
