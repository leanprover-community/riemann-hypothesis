import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingOfLam

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

theorem val_ratio {X X' Y Y₀ B : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X')} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb N φ' ε') (LB.LinComb L φ ε)) (h : Y ⟶ Y₀)
    (t : LB.Gen (LB.LinComb L (fun k => h ≫ φ k) ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb N (fun k => h ≫ φ' k) ε')) (ht' : t'.IsGen) (p : Y ⟶ B)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (e₁ : r ≫ h = r' ≫ h)
    (e₂ : r ≫ p = r' ≫ p) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good N z J') :
    val t r z J * (val t' r z J')⁻¹ = val t r' z J * (val t' r' z J')⁻¹ := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ (i : K → L.ι) (i' : K' → N.ι),
      LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' ≤
        h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart N φ' i') := fun i i' y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i i',
      r z ∈ LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart N (fun k => h ≫ φ' k) i' →
      gm r z _ (res inf_le_left (t.s i) * (res (le i i') (pullU h _ (w.s (i, i'))) * res inf_le_right (t'.s i'))⁻¹) =
        gm r z (LB.wchart L (fun k => h ≫ φ k) i) (t.s i) *
          (gm (r ≫ h) z (LB.wchart L φ i ⊓ LB.wchart N φ' i') (w.s (i, i')) *
            gm r z (LB.wchart N (fun k => h ≫ φ' k) i') (t'.s i'))⁻¹ :=
    fun Z r z i i' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z _ hz _).trans (gm_pull r h z _ (le i i' hz) _)) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y.Opens)
    (fun i : (K → L.ι) × (K' → N.ι) =>
      LB.wchart L (fun k => h ≫ φ k) i.1 ⊓ LB.wchart N (fun k => h ≫ φ' k) i.2) (fun _ => le_top)
    (fun y _ => by
      choose i hi using fun k => exists_chart hL (φ k (h y))
      choose i' hi' using fun k => exists_chart hN (φ' k (h y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), Set.mem_iInter.2 hi, Set.mem_iInter.2 hi'⟩)
    (fun i => res inf_le_left (t.s i.1) *
      (res (le i.1 i.2) (pullU h _ (w.s (i.1, i.2))) * res inf_le_right (t'.s i.2))⁻¹)
    (fun i j y hy => by
      have hm : (𝟙 Y ≫ h) y ∈ LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2 ⊓ (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) :=
        ⟨le _ _ hy.1, le _ _ hy.2⟩
      have e : gm (𝟙 Y ≫ h) y (LB.wchart L φ i.1 ⊓ LB.wchart N φ' i.2) (w.s (i.1, i.2)) =
          trF φ ε (𝟙 Y ≫ h) y i.1 j.1 * (trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2)⁻¹ *
            gm (𝟙 Y ≫ h) y (LB.wchart L φ j.1 ⊓ LB.wchart N φ' j.2) (w.s (j.1, j.2)) :=
        (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y ≫ h) y _) (hw (i.1, i.2) (j.1, j.2))).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·)
            ((gm_div (LB.LinComb N φ' ε') (LB.LinComb L φ ε) _ y (i.1, i.2) (j.1, j.2) hm).trans
              (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ ε _ y _ _ hm.1.1 hm.2.1)
                (gm_linComb N φ' ε' _ y _ _ hm.1.2 hm.2.2))) (gm_res _ y _ hm _))))
      have f₁ : trF φ ε (𝟙 Y ≫ h) y i.1 j.1 = trF (fun k => h ≫ φ k) ε (𝟙 Y) y i.1 j.1 := by
        simp only [trF, Category.assoc]
      have f₂ : trF φ' ε' (𝟙 Y ≫ h) y i.2 j.2 = trF (fun k => h ≫ φ' k) ε' (𝟙 Y) y i.2 j.2 := by
        simp only [trF, Category.assoc]
      refine (hv _ _ y _ _ hy.1).trans (Eq.trans ?_ (hv _ _ y _ _ hy.2).symm)
      rw [e, f₁, f₂,
        gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  obtain ⟨a, ha⟩ := hp c.val
  have hcv : ∀ r : Z ⟶ Y, (gm r z ⊤ c).val = gs (r ≫ p) z ⊤ a := fun r =>
    (gs_unit r z ⊤ trivial _).symm.trans ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a))
  have key : ∀ r : Z ⟶ Y, gm r z ⊤ c = val t r z J *
      (gm (r ≫ h) z (LB.wchart L φ (fun k => J ((r ≫ h) ≫ φ k)) ⊓ LB.wchart N φ' (fun k => J' ((r ≫ h) ≫ φ' k)))
        (w.s (fun k => J ((r ≫ h) ≫ φ k), fun k => J' ((r ≫ h) ≫ φ' k))) * val t' r z J')⁻¹ := fun r => by
    have hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) (fun k => J ((r ≫ h) ≫ φ k)) ⊓
        LB.wchart N (fun k => h ≫ φ' k) (fun k => J' ((r ≫ h) ≫ φ' k)) :=
      ⟨Set.mem_iInter.2 fun k => hJ ((r ≫ h) ≫ φ k), Set.mem_iInter.2 fun k => hJ' ((r ≫ h) ≫ φ' k)⟩
    rw [val_of t r z J (fun k => J ((r ≫ h) ≫ φ k)) (fun k => by rw [Category.assoc]),
      val_of t' r z J' (fun k => J' ((r ≫ h) ≫ φ' k)) (fun k => by rw [Category.assoc])]
    exact (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (_, _))).trans (hv Z r z _ _ hz))
  have q : gm r z ⊤ c = gm r' z ⊤ c := Units.ext (by rw [hcv, hcv, e₂])
  rw [key, key, e₁] at q
  apply Additive.ofMul.injective
  have q' := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_inv] at q' ⊢
  linear_combination (norm := abel) q'

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

theorem exists_gen_lam (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a g : B ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ B)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ B) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ B)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T B ≫ y) (snd T B ^ n)).left ≫
        (psum A ![fst B B ≫ a, snd B B ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T B ≫ y) (snd T B ^ n)).left ≫ (psum A ![fst B B ≫ a, snd B B ≫ g] I).left =
          (psum A ![fst T B ≫ y ≫ a, (snd T B ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T B ≫ y) (snd T B ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst B B ≫ a = fst T B ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd B B ≫ g = (snd T B ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T B).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T B ≫ y ≫ a).left)⁻¹ * h (fst T B ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T B) (snd T B ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T B) (snd T B ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T B).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ B, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

end GlobalTheory.PairingOfLam

namespace GlobalTheory

end GlobalTheory
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CM

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

variable {S : Scheme.{0}} {A B X Y : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj Y] [IsCommMonObj Y]

theorem exists_gen_lam_two (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : X ⟶ A) (g : Y ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ X)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ Y) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ Y)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫ (psum A ![fst X Y ≫ a, snd X Y ≫ g] I).left =
          (psum A ![fst T Y ≫ y ≫ a, (snd T Y ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T Y ≫ y) (snd T Y ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst X Y ≫ a = fst T Y ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd X Y ≫ g = (snd T Y ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T Y).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T Y ≫ y ≫ a).left)⁻¹ * h (fst T Y ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T Y) (snd T Y ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T Y) (snd T Y ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ Y, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

theorem weil_value_eq_of_lamEq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hY : IsAbelianScheme Y) {N : RigLB A} {L : RigLB B} (cN : CubicalStr A N) (cL : CubicalStr B L)
    (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) [IsMonHom f₂] [IsMonHom g₂]
    (H : LamEq N.L f₁ f₂ L.L g₁ g₂) {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ X)
    (z : T ⟶ Y) (hf : (y ≫ f₁) ^ n = 1) (hg : (y ≫ g₁) ^ n = 1) (hz : z ^ n = 1) (e e' : Γ(T.left, ⊤)ˣ)
    (he : WeilIs B L.L n (y ≫ g₁) (z ≫ g₂) e) (he' : WeilIs A N.L n (y ≫ f₁) (z ≫ f₂) e') : e = e' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨t, ht, v⟩ := exists_gen_lam_two hG hB cL p₀ hT g₁ g₂ n y hg
  obtain ⟨t', ht', v'⟩ := exists_gen_lam_two hG hA cN p₀ hT f₁ f₂ n y hf
  choose J hJ using fun χ : T.left ⟶ B.left => exists_chart L.isLB (χ p)
  choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := PairingOfLam.val_ratio L.isLB N.isLB H _ t ht t' ht' (fst T Y).left (WeilCube.surj_fst hG hY T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ Y)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ'
  rw [v z e hz he p J hJ, v' z e' hz he' p J' hJ'] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem weilEq_of_lamEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) := by
  intro hl k _ _ _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ H n x y c _ hx hy
  haveI := A.isAb.comm
  haveI := B.isAb.comm
  haveI := Y.isAb.comm
  obtain ⟨rA, hrA⟩ := A.rigid
  obtain ⟨rB, hrB⟩ := B.rigid
  obtain ⟨⟨cA⟩, -⟩ := hl.cube _ A ⟨A.L, rA, A.isLB, hrA⟩ rfl
  obtain ⟨⟨cB⟩, -⟩ := hl.cube _ B ⟨B.L, rB, B.isLB, hrB⟩ rfl
  let T : Over (Sp k) := Over.mk (𝟙 _)
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have h₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have h₃ : (x ≫ g₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₄ : (y ≫ g₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have key := weil_value_eq_of_lamEq hl.globalFns A.isAb B.isAb Y.isAb cA cB f₁ f₂ g₁ g₂ H p₀ hT n x y h₁ h₃ hy
  constructor
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ B n T).1 _ _ h₃ h₄
    exact key e _ he h ▸ he
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ A n T).1 _ _ h₁ h₂
    exact (key _ e h he).symm ▸ he

end GlobalTheory.CM
end
end
