import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSectionsOfNonzeroSpecial
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.PrimitiveExpansion

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem main : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  intro hL V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U σ ⟨x, hx, hn⟩
  obtain ⟨g, hE, hnd, H⟩ := GlobalTheory.NonzeroClosedFibre.main hL.1.globalFns V ϖ hϖ D Q hQ A G U σ
    (ThetaUnit.nonzeroOnSpecial_of_mem U σ x hx hn)
  have hgen := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd hL.1.secBaseChange V ϖ hϖ D (g 0)
    (fun ⟨g', h'⟩ => hnd ⟨g', fun j => (h' j).trans rfl⟩)
  refine ⟨fun s => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨Φ, hΦ, -⟩ := H (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ) (GlobalTheory.FamInt.valOver_ordVal hϖ)
    obtain ⟨b, hb⟩ := ThetaUnit.exists_eq_smul_group hL.1.globalFns le_rfl U hE
      (fun α => (ThetaUnit.secScal_one_iff D.toPre Φ α _).1 (hΦ α))
      (fun t => (hgen t).exists.imp fun b hb => (ThetaUnit.secIsMul_iff _ _ _ _).1 hb) s
    exact ⟨b, (ThetaUnit.secIsMul_iff _ _ _ _).2 hb⟩
  · obtain ⟨ϑ, hϑ, h₀, h₁⟩ := H F v hv
    refine ⟨ϑ, ⟨1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hE, secLin_one _
      (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_), fun α => secLin_one _ (hϑ α)⟩, h₀,
      fun r hr h => h₁ ⟨r, hr, h⟩⟩
    rw [Category.id_comp]
    exact (hσ' y J hJ).symm

end GlobalTheory.Ex.PrimitiveExpansion
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  atlas_forward_decl GlobalTheory.Ex.PrimitiveExpansion.main
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.GenericFibre

theorem exists_iso_section {X₁ X₂ Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {g : Y ⟶ X₁} {f : Y ⟶ X₂} (i : X₁ ⟶ Y)
    (hi : i ≫ g = 𝟙 X₁) (w₀ : LB.Iso (L₁.pull g) (L₂.pull f)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso L₁ (L₂.pull (i ≫ f)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
  have pt : ∀ x : X₁, g (i x) = x := fun x => congrArg (fun q : X₁ ⟶ X₁ => q x) hi
  have le : ∀ p : (PUnit → L₂.ι) × L₁.ι, (L₂.pull (i ≫ f)).U p.1 ⊓ L₁.U p.2 ≤
      i ⁻¹ᵁ ((L₂.pull f).U p.1 ⊓ (L₁.pull g).U (fun _ => p.2)) := fun p y hy =>
    ⟨mem_pull.2 ((mem_pull (F := i ≫ f)).1 hy.1), mem_pull.2 (by rw [pt]; exact hy.2)⟩
  let w : LB.Iso L₁ (L₂.pull (i ≫ f)) := ⟨fun p => res (le p) (pullU i _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
    intro Z r z j k hj hk
    have hm : r z ∈ (L₂.pull (i ≫ f)).U (fun _ => j) ⊓ L₁.U k := ⟨(mem_pull (F := i ≫ f)).2 hj, hk⟩
    exact (gm_res r z (le (fun _ => j, k)) hm _).trans (gm_pull r i z _ (le (fun _ => j, k) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, key⟩
  rw [key Z r z j k hj hk, key Z r z j' k' hj' hk',
    BoxExpansion.pw_trans hw (r ≫ i) z (j₁ := k) (j₁' := k') (j₂ := j) (j₂' := j')
      (by show g (i (r z)) ∈ _; rw [pt]; exact hk) (by show g (i (r z)) ∈ _; rw [pt]; exact hk') hj hj',
    Category.assoc, Category.assoc, hi, Category.comp_id]

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ z J, Good L z J → sval s' (𝟙 _) z J = sval s h z J := by
  subst e
  exact ⟨pullSec L φ ε s h, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_isoData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  intro R _ _ I D A G _ _ U
  obtain ⟨w₀, hw₀⟩ := U.ext
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hi' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨w, hw, key⟩ := exists_iso_section U.gen.inv.left hi w₀ hw₀
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK R)
  have hp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨ρ, hρ, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw U.LG.isLB A.isLB (ρ₀ := U.LG.rig) U.LG.rigGen
  refine ⟨w₀, ρ, w, hp, ⟨hw₀, hρ, fun z JA JG hA hG => ?_⟩, hw, hr, fun F _ _ k σ th H => ?_⟩
  · have e₁ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
      (cubeMapOf hp₁).e_comm.trans (Category.id_comp _)
    have e₂ : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G :=
      (cubeMapOf hp₂).e_comm
    have := hr _ (𝟙 _) z JG JA hG hA
    rw [Category.id_comp, Category.id_comp, wVal, key _ _ _ _ _ (hG (eSec A.A ≫ _ ≫ _)) (hA _), ← Category.assoc, e₁, e₂] at this
    exact this.symm
  · obtain ⟨σ', hσ⟩ := exists_pull_sec σ (UnifPre.gFK (G := G) F) (fun _ : Fin 1 => UnifPre.gFK (G := G) F)
      (funext fun _ => (Category.comp_id _).symm)
    have e : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    refine ⟨σ', hσ, fun s hs => ⟨σ', BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e (Category.id_comp _)
      fun y J₁ J₂ h₁ h₂ => ?_, hs⟩⟩
    have e' : ((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [e, Category.assoc, hi', Category.comp_id]
    have := H _ (U.genF F).left y J₂ J₁ h₂ h₁
    rw [wVal, key _ _ _ _ _ (h₂ (((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ _ ≫ _)) (h₁ _),
      ← Category.assoc, ← Category.assoc, e', e, zpow_natCast] at this
    exact (hσ y J₂ h₂).trans this

end GlobalTheory.Ex.GenericFibre
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  first | exact @GlobalTheory.Ex.GenericFibre.exists_isoData | exact GlobalTheory.Ex.GenericFibre.exists_isoData | (intros; apply GlobalTheory.Ex.GenericFibre.exists_isoData <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

theorem GlobalTheory.Ex.OneGen.thG_val_of_prim : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  rintro ⟨hLL, h₁, h₂, h₃, h₄⟩ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hw th ϑ hex hprim m hmo hmu hm
  have hAdm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨f, hf, hfs, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hLL V _ hAdm D A G hG U F (m ^ 2) (pow_pos hmo.pos 2)
  obtain ⟨ua, ub⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hLL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hw th ϑ hex hprim m hmo hmu
  refine ⟨fun x c H => ?_, ?_⟩
  · obtain ⟨hx, t, ht⟩ := (thG_iff A ρ m th x c).1 H
    obtain ⟨p, hp⟩ := hfs x hx
    refine (ua p x t c ((hf p x).2 hp.symm) ht).1 0 fun χ => div_nonneg ?_ (Nat.cast_nonneg _)
    by_cases h : m • χ + p.y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]; simp
    · exact_mod_cast zero_le_one.trans (QForm.Q_pos hϖ D hQ h)
  · obtain ⟨p', x', t, c, -, hx', -, hc, hz⟩ := ub m (by omega) dvd_rfl (TorusExt.qkZero D.tau_bimult F _) _ rfl
      ((hf _ _).2 rfl)
    exact ⟨x', c, (thG_iff A ρ m th x' c).2 ⟨(hx' w₀ hw.1).1, t, hc⟩, hz⟩
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → (∀ x (c : F), ThG A.A A.L ρ m th x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG A.A A.L ρ m th x (fnOf c) ∧ v c = 0 := by
  atlas_forward_decl GlobalTheory.Ex.OneGen.thG_val_of_prim
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OnModel

theorem mem_nonzeroLocus_pullTo {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) {y : Y'}
    (hy : h y ∈ nonzeroLocus s) : y ∈ nonzeroLocus (VVRank.pullTo s h e) := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  have hle := VVRank.wchart_le_of_eq (L := L) h e j
  have q := Y'.basicOpen_res ((h.app _).hom (s.f j)) (homOfLE hle).op
  refine q.ge ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Y.basicOpen_le _ hj) k, ?_⟩
  exact (Scheme.preimage_basicOpen h (s.f j)).le hj

section Base
variable {S : Scheme.{0}} (G : Over S)

def toBase : G.left ⟶ (Over.mk (𝟙 S) ⊗ G).left :=
  (lift (Over.homMk G.hom (Category.comp_id _) : G ⟶ Over.mk (𝟙 S)) (𝟙 G)).left

theorem toBase_snd : toBase G ≫ (snd (Over.mk (𝟙 S)) G).left = 𝟙 _ := by
  rw [toBase, ← Over.comp_left, lift_snd, Over.id_left]

theorem snd_hom : (snd (Over.mk (𝟙 S)) G).left ≫ G.hom = (fst (Over.mk (𝟙 S)) G).left :=
  (pullback.condition (f := 𝟙 S) (g := G.hom)).symm.trans (Category.comp_id _)

theorem comp_toBase {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) :
    (r ≫ (snd (Over.mk (𝟙 S)) G).left) ≫ toBase G = r := by
  have a : toBase G ≫ (fst (Over.mk (𝟙 S)) G).left = G.hom := by
    rw [toBase, ← Over.comp_left, lift_fst]; rfl
  refine psi_ext ?_ ?_
  · rw [Category.assoc, a, Category.assoc]
    exact congrArg (r ≫ ·) (snd_hom G)
  · rw [Category.assoc, toBase_snd, Category.comp_id]

variable [GrpObj G] {L : LB G.left} {k : ℕ}

def down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) : H0 L k :=
  VVRank.pullTo (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) G).left) (ε := fun _ => (k : ℤ)) σ (toBase G)
    fun _ => toBase_snd G

theorem sval_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left)
    (z : Z) {J} (hJ : Good L z J) :
    sval (down G σ) (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J = VVRank.sv G σ r z J := by
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [comp_toBase]

theorem mem_nonzeroLocus_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {g : (Over.mk (𝟙 S) ⊗ G).left}
    (hg : g ∈ nonzeroLocus σ) : (snd (Over.mk (𝟙 S)) G).left g ∈ nonzeroLocus (down G σ) := by
  refine mem_nonzeroLocus_pullTo _ _ _ ?_
  have e := comp_toBase G (𝟙 _)
  rw [Category.id_comp] at e
  rw [← Scheme.Hom.comp_apply, e]
  exact hg

end Base

theorem isGenSec_of_down {V : Type} [CommRing V] (G : Over (Sp V)) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 (Sp V))))) (h : ∀ s : H0 L k, ∃ b : V, SecIsMul G.hom b s (down G σ)) :
    IsGenSec G L (k : ℤ) σ := by
  intro s
  obtain ⟨b, hb⟩ := h (down G s)
  let c : Γ((Over.mk (𝟙 (Sp V))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b
  have key : SecM.ofSec G s = c • SecM.ofSec G σ := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine (sval_down G s (𝟙 _) y hJ).symm.trans (Eq.trans ?_ (congrArg (_ * ·) (sval_down G σ (𝟙 _) y hJ)))
    have hz := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ (snd (Over.mk (𝟙 (Sp V))) G).left)
    refine (congrArg (gs _ y _) (hb _)).trans ((gs_mul _ y _ hz _ _).trans (congrArg (· * _) ?_))
    refine (gs_res _ y le_top hz _).trans ((gs_pull _ G.hom y ⊤ trivial _).trans ?_)
    rw [Category.assoc, snd_hom]
  exact ⟨c, fun j => congrArg (fun q => q.1 j) key⟩

theorem theta_on_model : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hHV V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U σ hσ
  have hL := U.LG.isLB
  have := A.isAb.comm
  obtain ⟨g, hg, hg'⟩ := hσ
  obtain ⟨hgen, hexp⟩ := GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero hHV.1 V hc ϖ hϖ D Q hQ F v hv A G hG U (down G σ)
    ⟨_, by rw [← Scheme.Hom.comp_apply, snd_hom]; exact hg, mem_nonzeroLocus_down G σ hg'⟩
  refine ⟨isGenSec_of_down G hL σ hgen, fun m h₁ h₂ h₃ ξ => ?_⟩
  obtain ⟨w₀, ρ, w, hp, hN, hw, hr, H⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D A G U.toUnifPre
  have hτ : 𝟙 (Sp F) ≫ (Over.mk (jFK (R := V) F ≫ jK V)).hom = (TFK (R := V) F).hom ≫ jK V := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hp (T := TFK (R := V) F) (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) (𝟙 (Sp F)) hτ hw hL
    A.isLB (VVRank.pullS G _ ξ σ)
  obtain ⟨σ', hσ', hE⟩ := H F 1 (down G σ) th fun Z r z J J' hJ hJ' => by
    refine Eq.trans ?_ (hth Z r z J J' hJ hJ')
    refine Eq.trans ?_ ((sval_down G σ _ z hJ).trans (VVRank.sv_pullS G _ ξ σ _ z hJ).symm)
    rw [Category.assoc, VVRank.whisker_snd_left, Category.assoc, psi_snd']
  obtain ⟨ϑ, hϑ, hP⟩ := hexp σ' hσ'
  obtain ⟨k₁, x, c, k₂, k₃⟩ := GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit hHV V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ (hE ϑ hϑ) hP m h₁ h₂ h₃
  have hx : ∀ x : TFK (R := V) F ⟶ A.A, 𝟙 (Sp F) ≫ (pushHom hp (TFK (R := V) F) x).left = x.left ≫ _ :=
    fun x => Category.id_comp _
  refine ⟨fun x₀ c hc => ?_, pushHom hp (TFK (R := V) F) x, c, ?_, k₃⟩
  · let y : TFK (R := V) F ⟶ A.A := Over.homMk (hp.1.lift x₀.left (jFK (R := V) F) (Over.w x₀)) (hp.1.lift_snd _ _ _)
    have hy : 𝟙 (Sp F) ≫ x₀.left = y.left ≫ _ := (Category.id_comp _).trans (hp.1.lift_fst _ _ _).symm
    have hn : y ^ (m ^ 2) = 1 := by
      refine Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      refine (over_pow hp (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) _ hτ hy _).symm.trans ?_
      rw [hc.1]
      exact over_one hp _ hτ
    exact k₁ y c (ThG.move hp _ hτ hw hL A.isLB hr hy hn hth hc)
  · have : IsIso (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) := IsIso.id _
    have q := ThG.up hp _ hτ hw hL A.isLB hr (hx x) (by rw [← map_pow, k₂.1, map_one]) hth k₂
    have e : inv (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) = 𝟙 (Sp F) :=
      IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    rw [e] at q
    exact q

end GlobalTheory.Ex.OnModel
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OnModel.theta_on_model | exact GlobalTheory.Ex.OnModel.theta_on_model | (intros; apply GlobalTheory.Ex.OnModel.theta_on_model <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Rig
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]

theorem rigidification_map_on_values (m : CubeMap A G) {L₀ : LB G.left} {L₁ : LB A.left} (w : LB.Iso L₁ (L₀.pull m.F))
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) ρ₁ (m.rigPull L₀ ρ₀)) :
    IsRigidificationPullbackCompatibleIso w m.e ρ₁ ρ₀ := by
  have H := (maps_iff w _ (fun _ => eSec G) _ ρ₁ ρ₀ m.e _ (rigPull_le m.F m.e m.e_comm L₀) (fun _ => rfl)).1 h
  intro Z r z J J' hJ hJ'
  have e : (r ≫ m.e) ≫ eSec G = (r ≫ eSec A) ≫ m.F := by rw [Category.assoc, Category.assoc, m.e_comm]
  refine (val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ m.e) z J
    (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => congrArg J e)).trans ?_
  refine (H Z r z (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => J' (r ≫ eSec A)) (fun _ => hJ _) (fun _ => hJ' _)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

end Rig

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem mem_nonzeroLocus_iff_sv {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J} (hJ : Good L₁ z J) : r z ∈ nonzeroLocus s ↔ IsUnit (VVRank.sv A s r z J) := by
  have hz := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hz' : r z ∈ (LPow A L₁ a T).U k := (T ⊗ A).left.basicOpen_le _ hk
    have hu := (MulFinite.isUnit_gs r z _ hz' _).2 hk
    have e := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z hz' hz
    exact isUnit_of_mul_isUnit_right (e ▸ hu :)
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, (MulFinite.isUnit_gs r z _ hz _).1 h⟩

theorem SecRel.mem_nonzeroLocus (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {s : LB.Sec (LPow A L₁ a T)}
    {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀) (y : (T ⊗ A).left)
    (hy : psi hp τ hτ y ∈ nonzeroLocus s₀) : y ∈ nonzeroLocus s := by
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := (mem_nonzeroLocus_iff_sv s₀ (𝟙 _ ≫ psi hp τ hτ) y hJ).1 hy
  rw [h _ _ _ _ _ hJ hJ'] at q
  exact (mem_nonzeroLocus_iff_sv s (𝟙 _) y hJ').2 (isUnit_of_mul_isUnit_right q)

theorem SecRel.pullS {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (τ' : T'.left ⟶ T₀'.left) (hτ' : τ' ≫ T₀'.hom = T'.hom ≫ f) (ξ : T' ⟶ T)
    (ξ₀ : T₀' ⟶ T₀) (e : τ' ≫ ξ₀.left = ξ.left ≫ τ) :
    SecRel hp τ' hτ' w (VVRank.pullS A a ξ s) (VVRank.pullS G a ξ₀ s₀) := by
  intro Z r z J J' hJ hJ'
  have e' : psi hp τ' hτ' ≫ (ξ₀ ▷ G).left = (ξ ▷ A).left ≫ psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
        Category.assoc, Category.assoc, psi_fst', e, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, whiskerRight_fst]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
        VVRank.whisker_snd_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, VVRank.sv_pullS _ _ _ _ _ _ hJ', Category.assoc, e', ← Category.assoc,
    h _ _ _ _ _ hJ hJ', Category.assoc, VVRank.whisker_snd_left]

include hp hτ in

theorem exists_pt_down (x₀ : T₀ ⟶ G) {n : ℕ} (hn : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc)
  have hx : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ hc).symm
  refine ⟨x, hx, Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  rw [← over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

include hp hτ in

theorem exists_pt_up [IsIso τ] (x : T ⟶ A) {n : ℕ} (hn : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, Over.w_assoc, ← hτ, IsIso.inv_hom_id_assoc])
  have hx : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, hx, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

end Move

theorem theta_at_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hV E _ _ _ H S t V _ _ _ hC χ t' m P σ hσ
  obtain ⟨hD, hA, hZ⟩ := hC
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have hR : IsRigidificationPullbackCompatibleIso w χ t'.PP.rig t.PP.rig := by
    have q := rigidification_map_on_values m.cm w hr
    rw [m.base] at q
    exact q
  have hp := m.cart
  have hL₀ := t.PP.isLB
  have hL₁ := t'.PP.isLB
  let τ : (Over.mk (𝟙 (Sp V))).left ⟶ (Over.mk χ).left := 𝟙 (Sp V)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp V)))
  have hτ : τ ≫ (Over.mk χ).hom = (Over.mk (𝟙 (Sp V))).hom ≫ χ := rfl
  obtain ⟨σ', hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ σ
  have hσ' : NZ t'.G t'.PP.L (𝟙 (Sp V)) σ' := by
    obtain ⟨g, hg, hg'⟩ := hσ
    obtain ⟨κ, -, h₂⟩ := ThetaPtUp.exists_psi_inv' hp τ hτ
    have e : psi hp τ hτ (κ g) = g := congrArg (fun q => q g) h₂
    refine ⟨κ g, ?_, SecRel.mem_nonzeroLocus hp τ hτ hL₀ hL₁ hs _ (e.symm ▸ hg')⟩
    have e' := congrArg (fun q => q (κ g)) (psi_fst' hp τ hτ)
    exact e'.symm.trans ((congrArg (fst (Over.mk χ) t.G).left e).trans hg)
  have key : ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → IsGenSec t'.G t'.PP.L ((1 : ℕ) : ℤ) σ' ∧ ∀ n : ℕ, Odd n →
      IsUnit (n : V) → 3 ≤ n → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))),
      (∀ x (c : F), ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) → 0 ≤ v c) ∧
      ∃ x, ∃ c : F, ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) ∧ v c = 0 := by
    intro ϖ hϖ F _ _ _ v hv
    choose Q hQ using QForm.exists_QVal hϖ P.D
    have q := GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing hV V hA ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U
    dsimp only at q
    rw [P.bundle] at q
    exact q σ' hσ'
  refine ⟨?_, fun ϖ hϖ F _ _ _ v hv n h₁ h₂ h₃ x' ξ hξ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
    exact ThetaPtUp.isGenSec_up hp τ hτ hw hL₀ hL₁ hs (key ϖ hϖ _ v hv).1
  · let ξ' : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V)) :=
      Over.homMk (jFK (R := V) F ≫ jK V) (Category.comp_id _)
    obtain ⟨k₁, x, c, k₂, k₃⟩ := (key ϖ hϖ F v hv).2 n h₁ h₂ h₃ ξ'
    let τ' : (Over.mk (jFK (R := V) F ≫ jK V)).left ⟶ (Over.mk x').left := 𝟙 (Sp F)
    haveI : IsIso τ' := inferInstanceAs (IsIso (𝟙 (Sp F)))
    have hτ' : τ' ≫ (Over.mk x').hom = (Over.mk (jFK (R := V) F ≫ jK V)).hom ≫ χ :=
      (Category.id_comp _).trans ((Over.w ξ).symm.trans (congrArg (· ≫ χ) hξ))
    have hs' := SecRel.pullS hp τ hτ hs τ' hτ' ξ' ξ
      ((Category.id_comp _).trans (hξ.trans (Category.comp_id _).symm))
    have hi : inv τ' = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    refine ⟨fun y₀ d hd => ?_, ?_⟩
    · obtain ⟨y, hy, hn⟩ := exists_pt_down hp τ' hτ' y₀ hd.1
      exact k₁ y d (ThG.move hp τ' hτ' hw hL₀ hL₁ hR hy hn hs' hd)
    · obtain ⟨x₀, hx, hn⟩ := exists_pt_up hp τ' hτ' x k₂.1
      have q := ThG.up hp τ' hτ' hw hL₀ hL₁ hR hx hn hs' k₂
      rw [hi] at q
      exact ⟨x₀, c, q, k₃⟩

end GlobalTheory.Ex.OneGen
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_at_uniformised_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OneGen.theta_at_trait | exact GlobalTheory.Ex.OneGen.theta_at_trait | (intros; apply GlobalTheory.Ex.OneGen.theta_at_trait <;> assumption)
end
