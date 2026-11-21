import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodicStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationFormOfLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoCubeLBOfWeilIsAdjoint
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PairingOfForm

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing PrimNorm AdjointOfPairing

def chartUnflat {X Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
    ChartPull (LB.LinComb L (fun p : K' × K => ψ p.1 ≫ φ p.2) (fun p => ε p.2 * δ p.1))
      (LB.LinComb (LB.LinComb L φ ε) ψ δ) (𝟙 Z) :=
  have le : ∀ j : K' × K → L.ι, LB.wchart L (fun p : K' × K => ψ p.1 ≫ φ p.2) j ≤
      LB.wchart (LB.LinComb L φ ε) ψ (fun a b => j (a, b)) := fun j y hy =>
    Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (a, b)
  { idx := fun j a b => j (a, b)
    le := le
    g := fun y p q hp hq => by
      refine (gm_linComb L _ _ (𝟙 Z) y p q hp hq).trans (Eq.trans ?_
        (gm_linComb (LB.LinComb L φ ε) ψ δ (𝟙 Z) y _ _ (le p hp) (le q hq)).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => Eq.symm ?_
      refine (congrArg (· ^ δ k) (gm_linComb L φ ε (𝟙 Z ≫ ψ k) y (fun b => p (k, b)) (fun b => q (k, b))
        (Set.mem_iInter.1 (le p hp) k) (Set.mem_iInter.1 (le q hq) k))).trans ?_
      simp only [← Finset.prod_zpow, zpow_mul, Category.assoc] }

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem weilIs_swap {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A L k x y c) : WeilIs A L k y x c⁻¹ := by
  intro p
  obtain ⟨V, hp, ⟨θx, θy, h1, h2⟩, h3⟩ := h p
  refine ⟨V, hp, ⟨θy, θx, h2, h1⟩, fun θ₁ θ₂ e₁ e₂ => ?_⟩
  have H := h3 θ₂ θ₁ e₂ e₁
  unfold CommIsOf at H ⊢
  refine corr_of_val hL fun q J hJ => ?_
  have e := val_corr hJ H (𝟙 _)
  simp only [val_mul hJ, H1.val_constGen, unitRes, map_inv] at e ⊢
  rw [e, mul_inv_cancel_right]

abbrev fr {X Y : Scheme.{0}} (ψ : Y ⟶ X) : Abelianization (FreeGroup (Y ⟶ X)) := Abelianization.of (FreeGroup.of ψ)

def charSums (L : LB A.left) (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    Subgroup (Abelianization (FreeGroup ((T ⊗ A).left ⟶ A.left)) × Γ(T.left, ⊤)ˣ) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L φ ε)), u.IsGen ∧ ∏ k, fr (φ k) ^ ε k = s.1 ∧
      ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L z J →
        val u (lift t ((t ≫ x) * w)).left z J = val u (lift t w).left z J * gm t.left z ⊤ s.2}
  one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, fun _ _ => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    Fintype.prod_empty _, fun Z t w z J _ => by rw [val_one, val_one, Prod.snd_one, map_one, _root_.mul_one]⟩
  mul_mem' := by
    rintro ⟨_, c⟩ ⟨_, c'⟩ ⟨K, _, φ, ε, u, hu, rfl, h⟩ ⟨K', _, φ', ε', u', hu', rfl, h'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ u u', DVR.mulGen_isGen _ _ _ _ _ _ _ hu hu',
      Fintype.prod_sum_type _, fun Z t w z J hJ => ?_⟩
    rw [val_mul hJ, val_mul hJ, h Z t w z J hJ, h' Z t w z J hJ, Prod.snd_mul, map_mul, _root_.mul_mul_mul_comm]
  inv_mem' := by
    rintro ⟨_, c⟩ ⟨K, _, φ, ε, u, hu, rfl, h⟩
    refine ⟨K, inferInstance, _, _, LB.invGen L _ _ u, DVR.invGen_isGen _ _ _ _ hu,
      by simp only [zpow_neg, Finset.prod_inv_distrib, Prod.fst_inv], fun Z t w z J hJ => ?_⟩
    rw [val_inv, val_inv, h Z t w z J hJ, Prod.snd_inv, map_inv, mul_inv]

variable {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)

theorem eq_one_of_mem (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {c : Γ(T.left, ⊤)ˣ}
    (h : (1, c) ∈ charSums L hL x) : c = 1 := by
  obtain ⟨K, _, φ, ε, u, hu, hs, ht⟩ := h
  have key : ∀ (U : Type) [CommGroup U] (f : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, f (φ k) ^ ε k = 1 := by
    intro U _ f
    have e := congrArg (Abelianization.lift (FreeGroup.lift f)) hs
    simpa [map_prod, map_zpow] using e
  set p := (fst T A).left with hp_def
  set e := (lift (𝟙 T) (1 : T ⟶ A)).left with he_def
  have hl : ∀ w : T ⟶ A, (lift (𝟙 T) w).left ≫ p = 𝟙 _ := fun w => by
    rw [hp_def, ← Over.comp_left, lift_fst, Over.id_left]
  have hfe : FormEq (fun k => (p ≫ e) ≫ φ k) ε φ ε := by
    intro U _ f
    rw [key U f]
    simpa using key U (fun ψ => f ((p ≫ e) ≫ ψ))
  obtain ⟨u', hu', hv⟩ := exists_gen hL hfe (LB.pullGen L φ ε u (p ≫ e)) (LB.isGen_pullGen L φ ε u hu _)
  have hall : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val u r z J = val u (r ≫ p ≫ e) z J := by
    intro Z r z J hJ
    rw [gen_unique hL p e (hl 1) (GlobalTheory.CommutatorPairing.surj_fst hG hA T) hu hu' ?_ Z r z J hJ,
      hv Z r z J hJ, val_pull hJ]
    intro y J' hJ'
    rw [hv _ e y J' hJ', val_pull hJ', ← Category.assoc, hl 1, Category.id_comp]
  have hz : ∀ z : T.left, gm (𝟙 T.left) z ⊤ c = 1 := by
    intro z
    obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
    have h1 := ht T (𝟙 T) 1 z J hJ
    rw [hall _ _ z J hJ, hall _ (lift (𝟙 T) 1).left z J hJ, ← Category.assoc, hl, ← Category.assoc, hl,
      Over.id_left] at h1
    exact mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
  apply Units.ext
  apply fn_ext
  intro z _
  rw [gs_unit _ z ⊤ (by simp) c, gs_unit _ z ⊤ (by simp) 1, hz z, map_one]

theorem pull_mem {B : Over S} {K : Type} [Fintype K] {φ : K → (B.left ⟶ A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (ρ : T ⊗ A ⟶ B) (c : Γ(T.left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (t : Z ⟶ T) (w : Z ⟶ A) (z : Z.left) (J), Good L z J →
      val u (lift t ((t ≫ x) * w) ≫ ρ).left z J = val u (lift t w ≫ ρ).left z J * gm t.left z ⊤ c) :
    (∏ k, fr (ρ.left ≫ φ k) ^ ε k, c) ∈ charSums L hL x := by
  refine ⟨K, inferInstance, fun k => ρ.left ≫ φ k, ε, LB.pullGen L φ ε u ρ.left,
    LB.isGen_pullGen L φ ε u hu ρ.left, rfl, fun Z t w z J hJ => ?_⟩
  rw [val_pull hJ, val_pull hJ]
  simpa only [Over.comp_left] using h Z t w z J hJ

private theorem gm_res_pullU_eq_gm_comp' {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (a : Y ⟶ X) (z : Z) (U : X.Opens)
    (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) (hz : r z ∈ W) (u : Γ(X, U)ˣ) :
    gm r z W (res h (pullU a U u)) = gm (r ≫ a) z U u := by
  rw [← gm_id_pull r z W hz, pullU_res₂, gm_rp₂ r a z U _ _ hz]

theorem const_mem (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : T ⟶ A) :
    (fr (fst T A ≫ a).left, 1) ∈ charSums L hL x := by
  obtain ⟨j₀, hj₀⟩ := LB.mem_of_cover hL (a.left p₀)
  set ψ := (fst T A ≫ a).left with hψ_def
  have hψ : ∀ y, ψ y ∈ L.U j₀ := fun y => by
    have e : (fst T A).left y = p₀ := hT _
    show a.left ((fst T A).left y) ∈ L.U j₀
    rw [e]
    exact hj₀
  have hle : ∀ i : PUnit → L.ι,
      (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i ≤ ψ ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U j₀) :=
    fun i y hy => ⟨Set.mem_iInter.1 hy PUnit.unit, hψ y⟩
  have h0 : ∀ y, y ∈ LB.wchart L (fun _ : PUnit => ψ) (fun _ => j₀) :=
    fun y => Set.mem_iInter.2 fun _ => hψ y
  refine ⟨PUnit, inferInstance, fun _ => ψ, fun _ => 1,
    ⟨fun i => res (hle i) (pullU ψ _ (L.g (i PUnit.unit) j₀))⟩, ?_, by simp, ?_⟩
  · intro i i'
    apply Units.ext
    apply fn_ext
    intro y hy
    rw [gs_unit _ y _ hy, gs_unit _ y _ hy]
    congr 1
    rw [map_mul]
    dsimp only
    rw [LB.res_res, LB.res_res, gm_rp₁ _ _ _ _ _ hy, gm_rp₁ _ _ _ _ _ hy]
    have g : gm (𝟙 _) y ((LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i ⊓
        (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).U i')
        ((LB.LinComb L (fun _ : PUnit => ψ) (fun _ => (1 : ℤ))).g i i') =
        ∏ k : PUnit, gm (𝟙 _ ≫ ψ) y (L.U (i k) ⊓ L.U (i' k)) (L.g (i k) (i' k)) ^ (1 : ℤ) :=
      gm_linComb L _ _ (𝟙 _) y i i' hy.1 hy.2
    rw [g]
    have e := trF_trans hL (fun _ : PUnit => ψ) (fun _ => (1 : ℤ)) (𝟙 _) y hy.1 hy.2 (h0 y)
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp] at e ⊢
    exact e.symm
  · intro Z t' w z J hJ
    have key : ∀ r : Z.left ⟶ (T ⊗ A).left,
        val (⟨fun i => res (hle i) (pullU ψ _ (L.g (i PUnit.unit) j₀))⟩ :
          LB.Gen (LB.LinComb L (fun _ : PUnit => ψ) (fun _ => 1))) r z J =
        gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U j₀) (L.g (J (r ≫ ψ)) j₀) := by
      intro r
      unfold val
      exact gm_res_pullU_eq_gm_comp' r ψ z _ _ _ (Good.mem hJ (fun _ : PUnit => ψ) r) _
    rw [key, key]
    have e : ∀ v : Z ⟶ A, (lift t' v).left ≫ ψ = (t' ≫ a).left := fun v => by
      rw [hψ_def, ← Over.comp_left, lift_fst_assoc]
    rw [e, e]
    simp

variable [IsCommMonObj A]

theorem diff_mem (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (hx : x ^ n = 1) (f : A ⟶ A) [IsMonHom f] (b : T ⟶ A)
    (hb : b ^ n = 1) (c : Γ(T.left, ⊤)ˣ) (hc : WeilIs A L.L n b (x ≫ f) c) :
    (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ f) (fst T A ≫ b), c) ∈ charSums L.L L.isLB x := by
  obtain ⟨u, hu, hU⟩ := AdjointOfPairing.exists_gen_pairing hG hA cb p₀ hT n b hb
  have hxf : (x ≫ f) ^ n = 1 := by
    rw [← show postHom f T x = x ≫ f from rfl, ← map_pow, hx, map_one]
  have h1 := pull_mem L.isLB x u hu (lift (fst T A) (snd T A ≫ f)) c (fun Z t w z J hJ => by
    have e := hU (x ≫ f) c hxf hc Z t (w ≫ f) z J hJ
    have l : ∀ v : Z ⟶ A, lift t v ≫ lift (fst T A) (snd T A ≫ f) = lift t (v ≫ f) := fun v => by
      rw [comp_lift, lift_fst, lift_snd_assoc]
    rw [l, l, MonObj.mul_comp, Category.assoc]
    exact e)
  have h2 := const_mem L.isLB x p₀ hT 1
  have h3 := const_mem L.isLB x p₀ hT b
  have h4 := (charSums L.L L.isLB x).mul_mem ((charSums L.L L.isLB x).mul_mem h1 h2)
    ((charSums L.L L.isLB x).inv_mem h3)
  convert h4 using 1
  refine Prod.ext ?_ (by simp)
  have hp : (snd T A ≫ f) ^ n = (snd T A ^ n) ≫ f := (map_pow (postHom f (T ⊗ A)) (snd T A) n).symm
  have h1' : fst T A ≫ (1 : T ⟶ A) = 1 := by simp
  simp only [Prod.fst_mul, Prod.fst_inv]
  rw [AdjointOfPairing.prod_mulT n b (fst T A) (snd T A ≫ f) (h := fr), hp, h1', mul_comm (fst T A ≫ b)]
  simp only [diff₂]
  exact mul_right_comm _ _ _

theorem eq_prod (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : RigLB A} (cb : CubicalStr A L)
    (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (hx : x ^ n = 1) (y : T ⟶ A) (hy : y ^ n = 1)
    {I : Type} [Fintype I] (φ : I → (A ⟶ A)) (hφ : ∀ i, IsMonHom (φ i)) (ε : I → ℤ) (s : A ⟶ A) [IsMonHom s]
    (hs : LBIso (abelian₂ A (LB.LinComb L.L (fun i => (φ i).left) ε)) (cubeLB A ![fst A A, snd A A ≫ s] L.L))
    (c : I → Γ(T.left, ⊤)ˣ) (hc : ∀ i, WeilIs A L.L n (x ≫ φ i) (y ≫ φ i) (c i)) (d : Γ(T.left, ⊤)ˣ)
    (hd : WeilIs A L.L n x (y ≫ s) d) : d = ∏ i, c i ^ ε i := by
  have hE : ∀ i, (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ φ i) (fst T A ≫ y ≫ φ i), (c i)⁻¹) ∈
      charSums L.L L.isLB x := by
    intro i
    haveI := hφ i
    have hb : (y ≫ φ i) ^ n = 1 := by
      rw [← show postHom (φ i) T y = y ≫ φ i from rfl, ← map_pow, hy, map_one]
    exact diff_mem x hG hA cb p₀ hT n hx (φ i) (y ≫ φ i) hb (c i)⁻¹ (weilIs_swap L.isLB (hc i))
  have hEd : (diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ 𝟙 A) (fst T A ≫ y ≫ s), d⁻¹) ∈
      charSums L.L L.isLB x := by
    have hb : (y ≫ s) ^ n = 1 := by
      rw [← show postHom s T y = y ≫ s from rfl, ← map_pow, hy, map_one]
    have hw := weilIs_swap L.isLB hd
    rw [← Category.comp_id x] at hw
    exact diff_mem x hG hA cb p₀ hT n hx (𝟙 A) (y ≫ s) hb d⁻¹ hw
  have hflat : LBIso (LB.LinComb L.L (fun p : ULift.{0} (Finset (Fin 2)) × I =>
        (psum A (x2 A) p.1.down).left ≫ (φ p.2).left) (fun p => ε p.2 * (-1) ^ (2 - p.1.down.card)))
      (LB.LinComb L.L (fun J : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ s] J.down).left)
        (fun J => (-1) ^ (2 - J.down.card))) := by
    have hN : LBIso (abelian₂ A (LB.LinComb L.L (fun i => (φ i).left) ε))
        (LB.LinComb L.L (fun p : ULift.{0} (Finset (Fin 2)) × I =>
          (psum A (x2 A) p.1.down).left ≫ (φ p.2).left) (fun p => ε p.2 * (-1) ^ (2 - p.1.down.card))) :=
      lbIso_nested L.isLB _ _ _ _ _ _ (prod_flat _ _ _ _).symm
    exact LBIso.trans (LB.isLB_linComb L.isLB _ _) (LB.isLB_linComb (LB.isLB_linComb L.isLB _ _) _ _)
      (LB.isLB_linComb L.isLB _ _) hN.symm hs
  obtain ⟨u, hu⟩ := NormRos.exists_gen_of_lbIso hflat
  have hF := pull_mem L.isLB x u hu (lift (snd T A ^ n) (fst T A ≫ y)) 1 (fun Z t w z J hJ => by
    have e : ∀ v : Z ⟶ A, lift t v ≫ lift (snd T A ^ n) (fst T A ≫ y) = lift (v ^ n) (t ≫ y) := fun v => by
      rw [comp_lift, lift_fst_assoc, comp_pow, lift_snd]
    have c1 : t ≫ (1 : T ⟶ A) = 1 := by simpa using comp_pow (1 : T ⟶ A) 0 t
    rw [e, e, mul_pow, ← comp_pow, hx, c1, _root_.one_mul, map_one, _root_.mul_one])
  have cubeP : ∏ J : ULift.{0} (Finset (Fin 2)), fr ((lift (snd T A ^ n) (fst T A ≫ y)).left ≫
      (psum A ![fst A A, snd A A ≫ s] J.down).left) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ 𝟙 A) (fst T A ≫ y ≫ s) := by
    rw [prod_square (lift (snd T A ^ n) (fst T A ≫ y)) (fst A A) (snd A A ≫ s) (h := fr), lift_fst,
      lift_snd_assoc, Category.comp_id, Category.assoc]
  have flatP : ∀ i, ∏ J : ULift.{0} (Finset (Fin 2)), fr ((lift (snd T A ^ n) (fst T A ≫ y)).left ≫
      (psum A (x2 A) J.down).left ≫ (φ i).left) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      diff₂ (fun q : T ⊗ A ⟶ A => fr q.left) ((snd T A ^ n) ≫ φ i) (fst T A ≫ y ≫ φ i) := by
    intro i
    have := hφ i
    have e := prod_square (lift (snd T A ^ n) (fst T A ≫ y)) (fst A A) (snd A A)
      (h := fun ψ => fr (ψ ≫ (φ i).left))
    simp only [Category.assoc] at e
    rw [show x2 A = ![fst A A, snd A A] from rfl, e, lift_fst, lift_snd]
    simp only [diff₂, ← Over.comp_left, MonObj.mul_comp, one_comp, Category.assoc]
  have hQ := (charSums L.L L.isLB x).mul_mem ((charSums L.L L.isLB x).mul_mem hEd
    ((charSums L.L L.isLB x).inv_mem ((charSums L.L L.isLB x).prod_mem
      (fun i (_ : i ∈ (Finset.univ : Finset I)) => (charSums L.L L.isLB x).zpow_mem (hE i) (ε i))))) ((charSums L.L L.isLB x).inv_mem hF)
  have hz1 : ∀ (a : Abelianization (FreeGroup ((T ⊗ A).left ⟶ A.left)) × (Γ(T.left, ⊤))ˣ) (m : ℤ),
      (a ^ m).1 = a.1 ^ m := fun _ _ => rfl
  have h1 := eq_one_of_mem L.isLB x hG hA (c := d⁻¹ * ∏ i, c i ^ ε i) (by
    convert hQ using 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_prod, hz1]
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [cubeP, Fintype.prod_prod_type, Finset.prod_comm]
      simp only [zpow_neg, Finset.prod_inv_distrib, zpow_mul', Finset.prod_zpow, flatP]
      exact (mul_inv_cancel _).symm
    · simp [Prod.snd_prod, Finset.prod_inv_distrib])
  rw [inv_mul_eq_one] at h1
  exact h1

end GlobalTheory.PairingOfForm

namespace GlobalTheory

open PairingOfForm in

theorem weilIs_of_formIs_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  intro hl hl2 K _ _ P I _ φ ε s k x y c hk hφ hF hx hy hc
  obtain ⟨t, ht⟩ := P.rigid
  letI := P.isAb.comm
  have := hF.1
  obtain ⟨cb⟩ := (hl.cube (Sp K) P (RigLB.mk P.L t P.isLB ht) rfl).1
  obtain ⟨d, hd, -⟩ := (hl.weil (Sp K) P k (Out.baseOver (Sp K))).1 x (y ≫ s) hx (by
    rw [← show PrimNorm.postHom s _ y = y ≫ s from rfl, ← map_pow, hy, map_one])
  have hsub : Subsingleton (Out.baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Out.baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e := PairingOfForm.eq_prod x hl.globalFns P.isAb cb p₀ (fun p => Subsingleton.elim p p₀) k hx y hy φ hφ
    ε s hF.2 (fun i => unitOn (c i)) hc d hd
  have hu : unitOn (∏ i, c i ^ ε i) = ∏ i, unitOn (c i) ^ ε i := by
    unfold unitOn
    simp [map_prod, map_zpow]
  rw [hu, ← e]
  exact hd

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_of_polarisationForm_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  atlas_forward_decl GlobalTheory.weilIs_of_formIs_linComb
end

section
namespace GlobalTheory.RelationPowers

theorem rel_pow {G U : Type} [Monoid G] [Monoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (x : G) (c : U) (h : R x c) (k : ℕ) : R (x ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hmul _ _ _ _ ih h

theorem rel_prod_pow {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hmul _ _ _ _ (rel_pow R h1 hmul _ _ (h 0) _)
      (ih (fun i => y i.succ) (fun i => c i.succ) (fun i => a i.succ) (fun i => h i.succ))

end GlobalTheory.RelationPowers
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormTorsion

theorem rel_prod {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hm : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c')) :
    ∀ (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ), (∀ i, R (y i) (c i)) →
      R (List.ofFn fun i => y i ^ a i).prod (∏ i, c i ^ a i) := by
  first
  | exact @_root_.GlobalTheory.RelationPowers.rel_prod_pow
  | exact _root_.GlobalTheory.RelationPowers.rel_prod_pow
  | (apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationPowers.rel_prod_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationPowers.rel_prod_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationPowers.rel_prod_pow ..)

theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem weilIs_linComb (hW : Out.WeilSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ) {n : ℕ}
    (y : Fin n → (Out.baseOver (Sp K) ⟶ P.A)) (z : Out.baseOver (Sp K) ⟶ P.A) (hz : z ^ k = 1)
    (e : Fin n → ℤ) (a : Fin n → ℕ) (h : ∀ i, Out.WeilIs P.A P.L k (y i) z (unitOn (ζ ^ e i))) :
    Out.WeilIs P.A P.L k (Out.linComb y a) z (unitOn (ζ ^ ∑ i, (a i : ℤ) * e i)) := by
  obtain ⟨hu, hm, -, -⟩ := hW (Sp K) P k (Out.baseOver (Sp K))
  have h1 : Out.WeilIs P.A P.L k 1 z 1 := by
    obtain ⟨c, hc, hc'⟩ := hu 1 z (one_pow k) hz
    have h2 := hm _ _ _ _ _ hc hc
    rw [_root_.mul_one] at h2
    have : c = 1 := mul_eq_left.1 (hc' _ h2)
    exact this ▸ hc
  have H := rel_prod (fun x (c : Kˣ) => Out.WeilIs P.A P.L k x z (unitOn c))
    (by
      have : unitOn (1 : Kˣ) = 1 := map_one _
      show Out.WeilIs P.A P.L k 1 z (unitOn 1)
      rw [this]; exact h1)
    (fun x x' c c' hx hx' => by
      have : unitOn (c * c') = unitOn c * unitOn c' := map_mul _ _ _
      show Out.WeilIs P.A P.L k (x * x') z (unitOn (c * c'))
      rw [this]; exact hm _ _ _ _ _ hx hx') n y (fun i => ζ ^ e i) a h
  have e' : ∏ i, (ζ ^ e i) ^ a i = ζ ^ ∑ i, (a i : ℤ) * e i := by
    have key : ∀ t : Finset (Fin n), ∏ i ∈ t, (ζ ^ e i) ^ a i = ζ ^ ∑ i ∈ t, (a i : ℤ) * e i := fun t => by
      induction t using Finset.induction_on with
      | empty => simp
      | insert b t hb ih =>
        rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add, ← zpow_natCast, ← zpow_mul,
          _root_.mul_comm (e b)]
    exact key _
  rw [← e']
  exact H

theorem weilIs_symm_zpow {K : Type} [Field K] (P : Out.PolAV (Sp K)) (k : ℕ) (ζ : Kˣ)
    {x y : Out.baseOver (Sp K) ⟶ P.A} {e : ℤ} (h : Out.WeilIs P.A P.L k x y (unitOn (ζ ^ e))) :
    Out.WeilIs P.A P.L k y x (unitOn (ζ ^ (-e))) := by
  have : unitOn (ζ ^ (-e)) = (unitOn (ζ ^ e))⁻¹ := by
    rw [zpow_neg]; exact map_inv _ _
  rw [this]
  exact GlobalTheory.CommPairing.weilIs_symm P.isLB h

theorem injective_stdSymp (g k : ℕ) :
    Function.Injective (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k)) := by
  intro x x' h
  apply GlobalTheory.injective_toBilin'_stdSymp (R := ZMod k) g
  ext a
  have := congrFun h a
  simpa [Matrix.toBilin'_apply, Pi.single_apply] using this

theorem exists_matrix_form : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  intro hL hL2 g N k Mat
  classical
  refine ⟨fun i j => Function.invFun
    (fun (x : Fin (2 * g) → ZMod k) a => ∑ l, x l * ((Out.stdSymp g l a : ℤ) : ZMod k))
    (fun a => -(((Out.stdSymp g a j : ℤ) : ZMod k) * N +
      (∑ i, Mat i a * -(∑ l, Mat l j * ((Out.stdSymp g l i : ℤ) : ZMod k))) * N)) i, ?_⟩
  intro K _ _ P pt ζ f s hk hζ hB hpt hf hM hs
  refine ⟨hB.pos, fun j => ?_⟩
  haveI : NeZero k := ⟨fun e => hk (by simp [e])⟩
  haveI := hs.isMonHom
  have tors : ∀ (u : P.A ⟶ P.A) [IsMonHom u] i, (pt i ≫ u) ^ k = 1 := fun u _ i => by
    have := congrArg (IsMonHom.monoidHom u _) (hB.pow_eq_one i)
    rw [map_pow, map_one] at this
    exact this
  obtain ⟨c, hc, -⟩ := hB.existsUnique (tors s j)
  rw [← hc]
  congr 1
  funext i
  congr 1
  refine congrFun (?_ : c = _) i
  rw [← Function.leftInverse_invFun (injective_stdSymp g k) c]
  congr 1
  funext a
  have w₁ := weilIs_linComb hL.weil P k ζ pt (pt a) (hB.pow_eq_one a) _ (fun i => (c i).val) (fun i => hpt i a)
  rw [hc] at w₁
  have w₂ : ∀ i, Out.WeilIs P.A P.L k (pt i) (pt j ≫ f)
      (unitOn (ζ ^ (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i))) := fun i => by
    rw [hM.comp_eq j]
    exact weilIs_symm_zpow P k ζ (weilIs_linComb hL.weil P k ζ pt (pt i) (hB.pow_eq_one i) _ _ (fun l => hpt l i))
  have w₃ := weilIs_linComb hL.weil P k ζ pt _ (tors f j) _ (fun i => (Mat i a).val) w₂
  rw [← hM.comp_eq a] at w₃
  have eφ : (fun i : Fin 2 => ((![𝟙 P.A, f] : Fin 2 → (P.A ⟶ P.A)) i).left) = ![𝟙 P.A.left, f.left] := by
    funext i; fin_cases i <;> rfl
  have w₄ := GlobalTheory.T.weilPairing_of_polarisationForm_linComb hL hL2 K P (Fin 2) ![𝟙 P.A, f] ![(N : ℤ), (N : ℤ)] s k (pt a) (pt j)
    ![ζ ^ Out.stdSymp g a j, ζ ^ ∑ i, ((Mat i a).val : ℤ) * (-∑ l, ((Mat l j).val : ℤ) * Out.stdSymp g l i)] hk
    (fun i => by
      fin_cases i
      · exact (inferInstance : IsMonHom (𝟙 P.A))
      · exact hf)
    (by rw [eφ]; exact hs) (hB.pow_eq_one a) (hB.pow_eq_one j)
    (fun i => by
      fin_cases i
      · show Out.WeilIs P.A P.L k (pt a ≫ 𝟙 _) (pt j ≫ 𝟙 _) _
        rw [Category.comp_id, Category.comp_id]
        exact hpt a j
      · exact w₃)
  rw [Fin.prod_univ_two] at w₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at w₄
  rw [← zpow_mul, ← zpow_mul, ← zpow_add] at w₄
  have w₅ := weilIs_symm_zpow P k ζ w₄
  have e := unitOn_inj (((hL.weil (Sp K) P k _).1 _ _ (tors s j) (hB.pow_eq_one a)).unique w₁ w₅)
  rw [← mul_inv_eq_one, ← zpow_sub, hζ.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at e
  push_cast at e
  simp only [ZMod.natCast_zmod_val] at e
  exact sub_eq_zero.1 e

end GlobalTheory.FormTorsion
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_torsion_basis_symplectic : Out.Laws → Out.Laws2 → ∀ (g N k : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k)), ∃ S : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod k), ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f s : P.A ⟶ P.A), (k : K) ≠ 0 → IsPrimitiveRoot ζ k → TorsBasis P.A k pt → (∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn (ζ ^ Out.stdSymp g i j))) → IsMonHom f → ActsBy pt f Mat → FormIs P (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) s → ActsBy pt s S := by
  atlas_forward_decl GlobalTheory.FormTorsion.exists_matrix_form
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.GraphVolume

open GlobalTheory.CechPic

private theorem sec_eq_sec_one_pow {X : Scheme.{0}} {A : LB X} (hA : A.IsLB) (s : A.Sec) :
    ∀ k : ℕ, ∃ u : (lbPow A (k + 1)).Sec, Out.nonzeroLocus u = Out.nonzeroLocus s := by
  intro k
  induction k with
  | zero =>
    have hA1 : (lbPow A (0 + 1)).IsLB := LB.isLB_linComb hA _ _
    refine exists_sec_nonzeroLocus_eq_of_lbIso hA1 hA ((cls_eq_iff hA1 hA).1 ?_) s
    rw [cls_lbPow hA _ hA1, zero_add, one_smul]
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih
    have hB : (lbPow A (k + 1)).IsLB := LB.isLB_linComb hA _ _
    have hC : (lbPow A (k + 1 + 1)).IsLB := LB.isLB_linComb hA _ _
    have hD : (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))).IsLB := LB.isLB_div hC hB
    have hI : LBIso (LB.div (lbPow A (k + 1 + 1)) (lbPow A (k + 1))) A := by
      refine (cls_eq_iff hD hA).1 ?_
      rw [cls_div hC hB hD, cls_lbPow hA _ hC, cls_lbPow hA _ hB, succ_nsmul, add_sub_cancel_left]
    obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hD hA hI s
    obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_inf_div hB hC t u
    exact ⟨w, by rw [hw, ht, hu, inf_idem]⟩

private theorem mem_nonzeroLocus_pullSec {X : Scheme.{0}} {L : LB X} (f : X ⟶ X) (n : ℕ) (s : (lbPow L n).Sec) (x : X)
    (hx : f.base x ∈ Out.nonzeroLocus s) :
    x ∈ Out.nonzeroLocus (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f) := by
  obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hx
  have hxj : x ∈ (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n : ℤ))).U j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
  rw [mem_nonzeroLocus_iff_isUnit _ hxj]
  have e : gs (𝟙 X) x _ ((ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s f).f j) = gs (𝟙 X ≫ f) x _ (s.f j) :=
    (gs_res _ x _ hxj _).trans (gs_pull _ f x _ hj _)
  rw [e]
  exact (mem_nonzeroLocus_iff_pull s (𝟙 X ≫ f) x (by simpa using hj)).1 (by simpa using hx)

theorem isAmpleLB_graph {X : Scheme.{0}} {L : LB X} (hL : IsAmpleLB L) (f : X ⟶ X) {N : ℕ} (hN : 1 ≤ N) :
    IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) := by
  have hLB : L.IsLB := hL.isLB
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]).IsLB := LB.isLB_linComb hLB _ _
  refine { isLB := hM, compactSpace := hL.compactSpace, exists_affine := fun x => ?_ }
  obtain ⟨n1, hn1, s1, hx1, ha1⟩ := hL.exists_affine x
  obtain ⟨n2, hn2, s2, hx2, -⟩ := hL.exists_affine (f.base x)
  have hxt := mem_nonzeroLocus_pullSec f n2 s2 x hx2
  have hT : (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))).IsLB := LB.isLB_linComb hLB _ _
  have hA : (lbPow L n1).IsLB := LB.isLB_linComb hLB _ _
  obtain ⟨k1, hk1⟩ : ∃ k, k + 1 = n2 * N := ⟨n2 * N - 1, by have := Nat.mul_pos hn2 hN; omega⟩
  obtain ⟨k2, hk2⟩ : ∃ k, k + 1 = n1 * N := ⟨n1 * N - 1, by have := Nat.mul_pos hn1 hN; omega⟩
  obtain ⟨u1, hu1⟩ := sec_eq_sec_one_pow hA s1 k1
  obtain ⟨u2, hu2⟩ := sec_eq_sec_one_pow hT (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s2 f) k2
  have hA1 : (lbPow (lbPow L n1) (k1 + 1)).IsLB := LB.isLB_linComb hA _ _
  have hT2 : (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)).IsLB :=
    LB.isLB_linComb hT _ _
  have hB : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2)).IsLB :=
    LB.isLB_linComb hM _ _
  have hDv := LB.isLB_div hB hA1
  have hI : LBIso (LB.div (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) (n1 * n2))
      (lbPow (lbPow L n1) (k1 + 1)))
      (lbPow (LB.LinComb L (K := PUnit) (fun _ => f ≫ 𝟙 X) (fun _ => (n2 : ℤ))) (k2 + 1)) := by
    refine (cls_eq_iff hDv hT2).1 ?_
    rw [cls_div hB hA1 hDv, cls_lbPow hM _ hB, cls_lbPow hA _ hA1, cls_lbPow hLB _ hA, cls_lbPow hT _ hT2,
      cls_linComb hLB _ _ hM, cls_linComb hLB _ _ hT, Fin.sum_univ_two, hk1, hk2]
    simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      Category.comp_id, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨w, hw⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hDv hT2 hI u2
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_inf_div hA1 hB w u1
  refine ⟨n1 * n2, Nat.mul_pos hn1 hn2, v, ?_, ?_⟩
  · rw [hv, hw, hu2, hu1]
    exact ⟨hxt, hx1⟩
  · rw [hv, hw, hu2, hu1]
    exact isAffineOpen_nonzeroLocus_inf hT _ ha1

theorem exists_sec_ne_zero {X : Scheme.{0}} [Nonempty X] {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N κ : ℕ)
    (hD : IsAmpleLB (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1])) :
    ∃ n, 1 ≤ n ∧ ∃ s : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, s, hx, -⟩ := hD.exists_affine x
  refine ⟨n, hn, ?_⟩
  suffices H : ∃ v : (LB.div (lbPow (lbPow L (N * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]) n)).Sec, x ∈ Out.nonzeroLocus v by
    obtain ⟨v, hxv⟩ := H
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hxv
    refine ⟨v, k, fun h0 => ?_⟩
    have hb := (mem_nonzeroLocus_iff_basicOpen v hk).1 hxv
    rw [h0, Scheme.basicOpen_zero] at hb
    exact hb
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hLc : (lbPow L (0 * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
    have hLcn : (lbPow (lbPow L (0 * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
    have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]).IsLB := LB.isLB_linComb hL _ _
    have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)]) n).IsLB :=
      LB.isLB_linComb hM _ _
    have hQ := LB.isLB_div hLcn hMn
    obtain ⟨t, ht⟩ := (cls_eq_zero_iff hQ).1 (by
      rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
        cls_linComb hL _ _ hM, Fin.sum_univ_two]
      simp)
    refine ⟨DVR.genSec t ht, ?_⟩
    rw [nonzeroLocus_genSec hQ t ht]
    trivial
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hDL : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]).IsLB := hD.isLB
  have hDn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n).IsLB := LB.isLB_linComb hDL _ _
  obtain ⟨u, hu⟩ := sec_eq_sec_one_pow hDn s m
  have hDnm := LB.isLB_linComb hDn (K := PUnit) (fun _ => 𝟙 X) (fun _ => ((m + 1 : ℕ) : ℤ))
  have hLc : (lbPow L ((m + 1) * (1 + κ))).IsLB := LB.isLB_linComb hL _ _
  have hLcn : (lbPow (lbPow L ((m + 1) * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hM : (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]).IsLB :=
    LB.isLB_linComb hL _ _
  have hMn : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n).IsLB :=
    LB.isLB_linComb hM _ _
  have hQ := LB.isLB_div hLcn hMn
  have hI : LBIso (LB.div (lbPow (lbPow L ((m + 1) * (1 + κ))) n)
      (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![((m + 1 : ℕ) : ℤ), ((m + 1 : ℕ) : ℤ)]) n))
      (lbPow (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(κ : ℤ), -1]) n) (m + 1)) := by
    refine (cls_eq_iff hQ hDnm).1 ?_
    rw [cls_div hLcn hMn hQ, cls_lbPow hLc _ hLcn, cls_lbPow hL _ hLc, cls_lbPow hM _ hMn,
      cls_lbPow hDn _ hDnm, cls_lbPow hDL _ hDn, cls_linComb hL _ _ hM, cls_linComb hL _ _ hDL,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id]
    module
  obtain ⟨v, hv⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ hDnm hI u
  exact ⟨v, by rw [hv, hu]; exact hx⟩

theorem symB_graph {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (h : SymB L)
    (f : A ⟶ A) [IsMonHom f] (a b : ℤ) : SymB (LB.LinComb L (K := Fin 2) ![𝟙 A.left, f.left] ![a, b]) := by
  have hM := LB.isLB_linComb hL ![𝟙 A.left, f.left] ![a, b]
  have hMi := pull_isLB hM (GrpObj.inv : A ⟶ A).left
  have hLi := pull_isLB hL (GrpObj.inv : A ⟶ A).left
  have e0 : GlobalTheory.CechPic.pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
    rw [← cls_pull hL _ hLi]
    exact ((cls_eq_iff hL hLi).2 h).symm
  have e1 : (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  refine (cls_eq_iff hM hMi).1 ?_
  rw [cls_pull hM _ hMi, cls_linComb hL _ _ hM, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, GlobalTheory.CechPic.pull_id, map_add, map_zsmul]
  rw [e0, ← GlobalTheory.CechPic.pull_comp, e1, GlobalTheory.CechPic.pull_comp, e0]

theorem eq_of_sq_eq {k B a b : ℕ} (hB : B ^ 2 < k) (ha : a ≤ B) (hb : b ≤ B)
    (h : (a : ZMod k) ^ 2 = (b : ZMod k) ^ 2) : a = b := by
  have ha2 : a ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left ha 2) hB
  have hb2 : b ^ 2 < k := lt_of_le_of_lt (Nat.pow_le_pow_left hb 2) hB
  have h' : ((a ^ 2 : ℕ) : ZMod k) = ((b ^ 2 : ℕ) : ZMod k) := by push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h'
  exact Nat.pow_left_injective (by norm_num) h'

end GlobalTheory.GraphVolume

namespace GlobalTheory

open GraphVolume

theorem hilbert_graph_of_torsion : Out.Laws → Out.Laws2 → ∀ (g N κ l j : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (l ^ j))), 1 ≤ N → l.Prime → (N * (1 + κ)) ^ (2 * g) < l ^ j → ∃ δ ≤ (N * (1 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f : P.A ⟶ P.A), P.g = g → (l : K) ≠ 0 → IsPrimitiveRoot ζ (l ^ j) → TorsBasis P.A (l ^ j) pt → (∀ i i', Out.WeilIs P.A P.L ((l ^ j : ℕ) : ℤ) (pt i) (pt i') (unitOn (ζ ^ Out.stdSymp g i i'))) → IsMonHom f → ActsBy pt f Mat → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) → SymB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) e) (δ * e ^ g) := by
  intro hL1 hL2 g N κ l j Mat hN hl hB
  obtain ⟨S, hS⟩ := GlobalTheory.T.weil_pairing_torsion_basis_symplectic hL1 hL2 g N (l ^ j) Mat
  classical
  have hBk : ((N * (1 + κ)) ^ g) ^ 2 < l ^ j := by rw [← pow_mul, mul_comm g 2]; exact hB
  refine ⟨if h : ∃ d ≤ (N * (1 + κ)) ^ g, (d : ZMod (l ^ j)) ^ 2 = S.det then Classical.choose h else 0, ?_, ?_⟩
  · split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact Nat.zero_le _
  intro K _ _ P pt ζ f hg hl0 hζ hT hW hf hAct hD
  subst hg
  have := hf
  have hprop : IsProper P.A.hom := P.isAb.proper
  have hPL : P.L.IsLB := P.isLB
  set M := LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)] with hMdef
  have hM : M.IsLB := LB.isLB_linComb hPL _ _
  have hSym : SymB M := symB_graph hPL (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL1 hL2 K P).2.2.1 f _ _
  have hAmpL : IsAmpleLB P.L := (relAmple_iff_isAmpleLB_of_isAffine P.A hPL).1 P.ample
  have hAmpM : IsAmpleLB M := isAmpleLB_graph hAmpL f.left hN
  have hRelM : Out.RelAmple P.A M := (relAmple_iff_isAmpleLB_of_isAffine P.A hM).2 hAmpM
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_polarisationForm_of_lineBundle hL1 hL2 K P M hM
  have hk : ((l ^ j : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hl0
  have hSs : ActsBy pt s S := hS K P pt ζ f s hk hζ hT hW hf hAct hs
  obtain ⟨δ, hVol, hH0, hdet⟩ := GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion hL1 hL2 K P M s l hl hl0 hM hRelM hSym hs
  have hδ2 : (δ : ZMod (l ^ j)) ^ 2 = S.det := hdet j pt S hT hSs

  have hc : 1 ≤ N * (1 + κ) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hDa : IsAmpleLB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) :=
    (relAmple_iff_isAmpleLB_of_isAffine P.A (LB.isLB_linComb hPL _ _)).1 hD
  have hne : Nonempty (𝟙_ (Over (Sp K))).left := by
    change Nonempty (Sp K)
    infer_instance
  have : Nonempty P.A.left := ⟨(η[P.A] : 𝟙_ (Over (Sp K)) ⟶ P.A).left.base (Classical.choice hne)⟩
  obtain ⟨n, hn, t, ht⟩ := exists_sec_ne_zero hPL f.left N κ hDa
  have hLc : (lbPow P.L (N * (1 + κ))).IsLB := LB.isLB_linComb hPL _ _
  have hLcn : (lbPow (lbPow P.L (N * (1 + κ))) n).IsLB := LB.isLB_linComb hLc _ _
  have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
  have V1 : Vol P.A.hom P.L P.g 1 := (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL1 hL2 K P).1
  have V2 : Vol P.A.hom (lbPow P.L (N * (1 + κ))) P.g (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P P.L P.g hPL).2.2.2.1 _ 1 hc V1
  have V3 : Vol P.A.hom (lbPow (lbPow P.L (N * (1 + κ))) n) P.g
      ((n : ℝ) ^ P.g * (((N * (1 + κ) : ℕ) : ℝ) ^ P.g * 1)) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hLc).2.2.2.1 n _ hn V2
  have V4 : Vol P.A.hom (lbPow M n) P.g ((n : ℝ) ^ P.g * (δ : ℝ)) :=
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P M P.g hM).2.2.2.1 n _ hn hVol
  have hle := ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (lbPow M n) P.g hMn).2.2.2.2.2 _ t hLcn ht).2 _ _ V4 V3
  have hnpos : (0 : ℝ) < (n : ℝ) ^ P.g := pow_pos (by exact_mod_cast hn) _
  have hδB : δ ≤ (N * (1 + κ)) ^ P.g := by
    have h1 : (δ : ℝ) ≤ ((N * (1 + κ) : ℕ) : ℝ) ^ P.g := by
      have := le_of_mul_le_mul_left (by simpa using hle) hnpos
      simpa using this
    exact_mod_cast h1
  have hex : ∃ d ≤ (N * (1 + κ)) ^ P.g, (d : ZMod (l ^ j)) ^ 2 = S.det := ⟨δ, hδB, hδ2⟩
  rw [dif_pos hex]
  have hsp := Classical.choose_spec hex
  have hEq : δ = Classical.choose hex := eq_of_sq_eq hBk hδB hsp.1 (hδ2.trans hsp.2.symm)
  rw [← hEq]
  exact ⟨hSym, hH0⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunction_endomorphismGraph_of_torsionAction : Out.Laws → Out.Laws2 → ∀ (g N κ l j : ℕ) (Mat : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (l ^ j))), 1 ≤ N → l.Prime → (N * (1 + κ)) ^ (2 * g) < l ^ j → ∃ δ ≤ (N * (1 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (pt : Fin (2 * g) → (Out.baseOver (Sp K) ⟶ P.A)) (ζ : Kˣ) (f : P.A ⟶ P.A), P.g = g → (l : K) ≠ 0 → IsPrimitiveRoot ζ (l ^ j) → TorsBasis P.A (l ^ j) pt → (∀ i i', Out.WeilIs P.A P.L ((l ^ j : ℕ) : ℤ) (pt i) (pt i') (unitOn (ζ ^ Out.stdSymp g i i'))) → IsMonHom f → ActsBy pt f Mat → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) → SymB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(N : ℤ), (N : ℤ)]) e) (δ * e ^ g) := by
  first | exact @GlobalTheory.hilbert_graph_of_torsion | exact GlobalTheory.hilbert_graph_of_torsion | (intros; apply GlobalTheory.hilbert_graph_of_torsion <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.GraphCut

abbrev graphLB {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (N : ℕ) : LB X :=
  LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![(N : ℤ), (N : ℤ)]

theorem cls_graphLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : X ⟶ X) (N : ℕ) (h : (graphLB L f N).IsLB) :
    cls _ h = N • cls L hL + N • pull f (cls L hL) := by
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp [pull_id]

theorem unitS_spMap {o K : Type} [CommRing o] [CommRing K] (β : o →+* K) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  exact (congrArg (fun φ => φ.hom (u : o)) h).symm

theorem vol_inv (H1 : Out.Laws) (H2 : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 1 ≤ N) :
    SymB (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) ∧
      ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow (graphLB P.L ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left N) e) ((N * 2) ^ P.g * e ^ P.g) := by
  have hi : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [hi]
  have hs : cls P.L P.isLB = pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) :=
    (cls_eq_iff P.isLB (pull_isLB P.isLB _)).2 (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample H1 H2 K P).2.2.1
  have hB : (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N).IsLB := LB.isLB_linComb P.isLB _ _
  have hc := cls_graphLB P.isLB _ N hB
  rw [← hs] at hc
  refine ⟨(cls_eq_iff hB (pull_isLB hB _)).1 ?_, fun e he => ?_⟩
  · rw [cls_pull hB, hc, map_add, map_nsmul, ← hs]
  · have h0 : SectionsHaveFiniteDimension P.A.hom (lbPow P.L (N * 2 * e)) ((N * 2 * e) ^ P.g) :=
      GlobalTheory.PowSec.exists_basis_sections H1.globalSectionsRank K P (N * 2 * e) (Nat.succ_le_of_lt (by positivity))
    rw [← mul_pow]
    have h1 : (lbPow P.L (N * 2 * e)).IsLB := LB.isLB_linComb P.isLB _ _
    have h2 : (lbPow (graphLB P.L (GrpObj.inv : P.A ⟶ P.A).left N) e).IsLB := LB.isLB_linComb hB _ _
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ h1).2.1 _ h2 ((cls_eq_iff h1 h2).1 ?_)).1 _ h0
    rw [cls_lbPow P.isLB, cls_lbPow hB, hc, ← add_nsmul, smul_smul]
    congr 1
    ring

theorem exists_vol (H1 : Out.Laws) (H2 : Out.Laws2) (g : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (κ N l m k : ℕ) (hk : k = l ^ m) (hm : m ≠ 0) (hN : 1 ≤ N) (hl : l.Prime) (hlt : (N * (1 + κ)) ^ (2 * g) < k)
    (o : Type) [CommRing o] (b : TBase o k) (i : Option J) :
    ∃ δ ≤ (N * (2 + κ)) ^ g, ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g k J b (spMap β))
      (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → TorsBasis t.A k t.pt →
      SymB (graphLB t.L f.left N) ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension t.A.hom (lbPow (graphLB t.L f.left N) e) (δ * e ^ g) := by
  subst hk
  cases i with
  | none =>
    refine ⟨(N * 2) ^ g, Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _, ?_⟩
    intro K _ _ β t f _ hf _
    subst hf
    exact vol_inv H1 H2 K t.pol N hN
  | some i =>
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.T.hilbertFunction_endomorphismGraph_of_torsionAction H1 H2 g N κ l m ((Mat i).map (Int.cast : ℤ → ZMod (l ^ m))) hN hl hlt
    refine ⟨δ, hδ.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) _), ?_⟩
    intro K _ _ β t f hS hf hT
    subst hf
    have hl0 : (l : K) ≠ 0 := by
      have := (b.unit.map β).ne_zero
      rw [map_natCast, Nat.cast_pow] at this
      exact fun h => this (by rw [h, zero_pow hm])
    refine H K t.pol t.pt (Units.map β.toMonoidHom b.ζ) (t.act i) rfl hl0
      (IsPrimitiveRoot.coe_units_iff.1 (b.prim K β)) hT (fun a a' => ?_) (t.hom i) ⟨hT.pos, (hS i).1⟩ (hS i).2
    have := t.pairing a a'
    rw [unitS_spMap] at this
    have e : unitOn ((Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a') =
      unitOn (Units.map β.toMonoidHom b.ζ) ^ Out.stdSymp g a a' := map_zpow (Units.map _) _ _
    rw [e]
    exact this

theorem lift_left_eq {S : Scheme.{0}} {A : Over S} [IsIso (snd (Over.mk (𝟙 S)) A).left] (y : Over.mk (𝟙 S) ⟶ A) :
    y.left ≫ inv (snd (Over.mk (𝟙 S)) A).left = (lift (𝟙 (Over.mk (𝟙 S))) y).left := by
  rw [IsIso.comp_inv_eq, ← Over.comp_left, lift_snd]

theorem pow_comp_graph {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Option J) {T : Over S} (x : T ⟶ t.A) (m : ℕ) :
    (x ^ m) ≫ i.elim (𝟙 t.A)⁻¹ t.act = (x ≫ i.elim (𝟙 t.A)⁻¹ t.act) ^ m := by
  cases i with
  | none => simp only [Option.elim_none, GrpObj.comp_inv, Category.comp_id, inv_pow]
  | some i =>
    haveI := t.hom i
    exact MonObj.pow_comp x m (t.act i)

theorem cutBy_graphIdeal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  intro H1 H2 g J _ Mat κ n hn hodd
  have hn2 : 2 ≤ n := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, Hc⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H1 H2 g ((n ^ 2) ^ 2 * (2 + κ)) (Ix g ((n ^ 2) ^ 2) × Ix g ((n ^ 2) ^ 2))
  refine ⟨2 + k₀ + ((n ^ 2) ^ 2 * (1 + κ)) ^ (2 * g), fun j hj o _ b i => ?_⟩
  have hjn : j < n ^ j := Nat.lt_pow_self hn2
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  obtain ⟨δ, hδ, Hv⟩ := exists_vol H1 H2 g J Mat κ ((n ^ 2) ^ 2) n (j * 2) ((n ^ j) ^ 2) (pow_mul n j 2).symm (by omega)
    (Nat.succ_le_of_lt (by positivity)) hn
    (lt_of_lt_of_le (lt_of_le_of_lt (by omega) hjn) (Nat.le_self_pow two_ne_zero _)) o b i
  let c : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ 2) ^ 2) := fun a u => ZMod.castHom hdvd2 (ZMod ((n ^ 2) ^ 2)) (a u)
  have hc : Function.Surjective c := fun a => by
    choose a' ha' using fun u => ZMod.castHom_surjective hdvd2 (a u)
    exact ⟨a', funext ha'⟩
  have hc' : ∀ a a', c a = c a' → ∀ u, (a u).val ≡ (a' u).val [MOD (n ^ 2) ^ 2] := fun a a' h u => by
    have := congrFun h u
    simp only [c, ZMod.castHom_apply, ZMod.cast_eq_val] at this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 this
  obtain ⟨Q, HQ⟩ := Hc δ hδ (Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) (Prod.map c c) (hc.prodMap hc)
  refine ⟨Q, d, fun K _ _ β t σ p q f hS hf hE hpq => ?_⟩
  obtain ⟨hiso, hLB, hVA, hpow, hper, hT, hsurj⟩ := GlobalTheory.T.thetaSections_veryAmple_periodic H1 H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (hn2.trans (Nat.le_self_pow two_ne_zero n)) hE
  obtain ⟨hsym, hH⟩ := Hv K β t f hS hf hT
  have ha₂ : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (fst (Over.mk (𝟙 (Sp K))) t.A).left =
      (fst (Over.mk (𝟙 (Sp K))) t.A).left := by rw [← Over.comp_left, lift_fst]
  have ha₂' : (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left =
      (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ f.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  obtain ⟨M, th, hM, hMVA, hMiso, hid, hco, hMper⟩ := GlobalTheory.ZV.GraphSystem.exists_product_system K _ _ _ _ _ (fst (Over.mk (𝟙 (Sp K))) t.A).left _ _ _ _ σ σ
    (𝟙 _) (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left hLB hLB hVA hVA inferInstance (Category.id_comp _) ha₂
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    ((Over.w (snd (Over.mk (𝟙 (Sp K))) t.A)).trans (Over.w (fst (Over.mk (𝟙 (Sp K))) t.A)).symm).trans (Category.comp_id _)
  have hB : (graphLB t.L f.left ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have hP : (lbPow t.L ((n ^ 2) ^ 2)).IsLB := LB.isLB_linComb t.isLB _ _
  have c₁ := (cls_eq_iff hLB (pull_isLB hP _)).2 hpow
  rw [cls_pull hP, cls_lbPow t.isLB] at c₁
  have c₂ := (cls_eq_iff (LB.isLB_div hM (pull_isLB hLB _)) (pull_isLB hLB _)).2 hMiso
  rw [cls_div hM (pull_isLB hLB _), cls_pull hLB, cls_pull hLB, pull_id, c₁, ← pull_comp, ha₂', pull_comp,
    sub_eq_iff_eq_add', ← map_add, map_nsmul, ← cls_graphLB t.isLB _ _ hB] at c₂
  have c₃ : cls (M.pull e.inv) (pull_isLB hM _) = cls _ hB := by
    rw [cls_pull hM, c₂, ← pull_comp]
    exact (congrArg (fun φ => pull φ (cls _ hB)) e.inv_hom_id).trans (pull_id _)
  rw [hid, ← he]
  refine HQ K t.pol rfl _ e M th (n ^ j) _ (fun h => t.lab h ^ n ^ j) _ hM ?_ (he ▸ hMVA) ?_ ?_ (by omega) ?_ hsurj ?_
  · refine (cls_eq_iff (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _)).1 ?_
    rw [cls_pull (pull_isLB hM _)]
    exact c₃.trans (((cls_eq_iff hB (pull_isLB hB _)).2 hsym).trans (congrArg (pull (GrpObj.inv : t.A ⟶ t.A).left) c₃.symm))
  · intro a a' h
    exact hMper a a' (hper _ _ (hc' _ _ (congrArg Prod.fst h))) (hper _ _ (hc' _ _ (congrArg Prod.snd h)))
  · intro m hm
    have h1 : (lbPow (graphLB t.L f.left ((n ^ 2) ^ 2)) m).IsLB := LB.isLB_linComb hB _ _
    have h2 : (lbPow M m).IsLB := LB.isLB_linComb hM _ _
    have h3 := ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ t.A.hom _ h1).2.2.2.2.2 _ e _).1 (hH m hm)
    refine ((GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ _ _ (pull_isLB h1 e.hom)).2.1 _ h2 ((cls_eq_iff (pull_isLB h1 _) h2).1 ?_)).1 _ h3
    rw [cls_pull h1, cls_lbPow hB, cls_lbPow hM, map_nsmul, c₂]
    rfl
  · have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow] at this
    exact fun h => this (by rw [h, zero_pow two_ne_zero])
  · intro h
    have hy : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := lift_left_eq _
    have hy' : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left ≫
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left =
        (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hf, pow_comp_graph]
    have := hco K (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) (q h)
      (by rw [Category.comp_id]; exact (hpq h).1) (by rw [hy']; exact (hpq h).2)
    rw [← hy] at this
    exact this

end GlobalTheory.GraphCut
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (i : Option J), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p q : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (f : t.A ⟶ t.A), t.Shape Mat κ → f = i.elim (𝟙 t.A)⁻¹ t.act → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h) ∧ SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ n ^ j)).left (q h)) → CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2) := by
  atlas_forward_decl GlobalTheory.GraphCut.cutBy_graphIdeal
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.EndBuild

theorem pow_val_natCast {A : Type} [Monoid A] {k : ℕ} (y : A) (hy : y ^ k = 1) (m : ℕ) :
    y ^ ((m : ZMod k)).val = y ^ m := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m hy]

def labMap {g : ℕ} {J : Type} (k : ℕ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (i : Option J) (h : Ix g k) : Ix g k :=
  i.elim (-h) (fun j i' => ((∑ c, (Mat j i' c : ZMod k).val * (h c).val : ℕ) : ZMod k))

theorem linComb_eq_prod {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ}
    (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) : Out.linComb y a = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]

theorem lab_comp {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} [NeZero k] {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (ht : t.Shape Mat κ)
    (i : Option J) (h : Ix g k) :
    t.lab h ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A) = t.lab (labMap k Mat i h) := by
  haveI := t.ab.comm
  cases i with
  | none =>
    simp only [Option.elim, labMap]
    rw [GrpObj.comp_inv, Category.comp_id]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [TObj.lab, TObj.lab, linComb_eq_prod, linComb_eq_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [← pow_add, ← pow_val_natCast _ (t.torsion c)]
    simp
  | some j =>
    simp only [Option.elim, labMap]
    haveI := t.hom j
    have e : t.lab h ≫ t.act j = ∏ c, (t.pt c ≫ t.act j) ^ (h c).val := by
      rw [TObj.lab, linComb_eq_prod]
      have := map_prod (IsMonHom.monoidHom (t.act j) (Out.baseOver S)) (fun c => t.pt c ^ (h c).val) Finset.univ
      simp only [map_pow] at this
      exact this
    rw [e, TObj.lab, linComb_eq_prod]
    simp only [(ht j).1, TObj.lab, linComb_eq_prod, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [pow_val_natCast _ (t.torsion c), Finset.prod_pow_eq_pow_sum]

theorem graphIdeal_le {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w → SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w → SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' ≤ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  unfold graphIdeal
  refine le_iInf fun T => le_iInf fun _ => le_iInf fun β => le_iInf fun y => le_iInf fun v₁ => le_iInf fun v₂ =>
    le_iInf fun hy => ?_
  refine iInf_le_of_le T <| iInf_le_of_le inferInstance <| iInf_le_of_le β <| iInf_le_of_le (y ≫ e) <|
    iInf_le_of_le v₁ <| iInf_le_of_le v₂ <| iInf_le_of_le ⟨?_, ?_, ?_⟩ le_rfl
  · rw [Category.assoc, he, hy.1]
  · rw [Category.assoc]; exact h₁ _ _ _ hy.2.1
  · rw [Category.assoc]; exact h₂ _ _ _ hy.2.2

theorem graphIdeal_eq {R σ₁ σ₂ : Type} [CommRing R] {Y Y' X₁ X₂ X₁' X₂' : Scheme.{0}} (s : Y ⟶ Sp R) (s' : Y' ⟶ Sp R)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (M₁' : LB X₁') (th₁' : σ₁ → M₁'.Sec) (a₁' : Y' ⟶ X₁') (M₂' : LB X₂') (th₂' : σ₂ → M₂'.Sec) (a₂' : Y' ⟶ X₂')
    (e : Y ⟶ Y') [IsIso e] (he : e ≫ s' = s)
    (h₁ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₁ → T),
      SecCoord M₁ th₁ (y ≫ a₁) w ↔ SecCoord M₁' th₁' (y ≫ e ≫ a₁') w)
    (h₂ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (w : σ₂ → T),
      SecCoord M₂ th₂ (y ≫ a₂) w ↔ SecCoord M₂' th₂' (y ≫ e ≫ a₂') w) :
    graphIdeal s' M₁' th₁' a₁' M₂' th₂' a₂' = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  refine le_antisymm (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he (fun T _ y w => (h₁ T y w).1)
    (fun T _ y w => (h₂ T y w).1)) (graphIdeal_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv e) (by rw [← he, IsIso.inv_hom_id_assoc])
    (fun T _ y w hw => ?_) (fun T _ y w hw => ?_))
  · rw [← Category.assoc, h₁]; simpa using hw
  · rw [← Category.assoc, h₂]; simpa using hw

theorem cut_fibre {o R K : Type} [CommRing o] [CommRing R] [Field K] {g N m : ℕ} [NeZero (N ^ 2)] {J : Type}
    {b : TBase o (N ^ 2)} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} (i : Option J) (Q : Polynomial ℚ) (d : ℕ)
    {s : Sp K ⟶ Sp o} (t : TObj g (N ^ 2) J b s) (ht : t.Shape Mat κ)
    (σ : Ix g (N ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
    (hcut : ∀ (p q : Ix g (N ^ 2) → Ix g (N ^ 2) → K) (f : t.A ⟶ t.A), f = i.elim (𝟙 t.A)⁻¹ t.act →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (p h) ∧
        SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) ((t.lab h ≫ f) ^ N)).left (q h)) →
      CutBy (graphIdeal (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _) _ σ
        (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ f)).left) Q d (fun h i => p h i.1 * q h i.2))
    (Z : Over (Sp R)) (M : LB Z.left) (hM : M.IsLB) (th : Ix g (N ^ 2) → M.Sec)
    (sc : Ix g (N ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g (N ^ 2) → Ix g (N ^ 2) → R)
    (hp : ∀ h, SecCoord M th (sc h).left (p h)) (x : R →+* K) (φ : t.A.left ⟶ Z.left)
    (hφ : IsPullback φ t.A.hom Z.hom (spMap x))
    (hσ : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left) (w : Ix g (N ^ 2) → T),
      SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w)
    (hl : ∀ h, (t.lab h ^ N).left ≫ φ = spMap x ≫ (sc h).left) :
    CutBy (graphIdeal (pullback.snd Z.hom (spMap x)) M th (pullback.fst _ _) M th
      (hφ.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ)) Q d
      (fun h c => x (p h c.1 * p (labMap (N ^ 2) Mat i h) c.2)) := by
  have hpt : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left (fun a => x (p h a)) := by
    intro h
    refine (hσ K _ _).2 ?_
    have e : (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N)).left ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ =
        spMap x ≫ (sc h).left := by
      rw [← hl h, ← Category.assoc, ← Over.comp_left, lift_snd]
    have := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ M _ th R (sc h).left (p h) hM (hp h)).1 K x
    exact e ▸ this
  have H := hcut (fun h a => x (p h a)) (fun h a => x (p (labMap (N ^ 2) Mat i h) a)) _ rfl
    (fun h => ⟨hpt h, by rw [lab_comp t ht]; exact hpt _⟩)
  haveI : IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom))
  have hs : (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    (pullback.condition (f := 𝟙 (Sp K)) (g := t.A.hom)).symm.trans (Category.comp_id _)
  rw [graphIdeal_eq (fst (Over.mk (𝟙 (Sp K))) t.A).left (pullback.snd Z.hom (spMap x)) _ σ (𝟙 _) _ σ
    (lift (fst _ _) (snd (Over.mk (𝟙 (Sp K))) t.A ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A))).left M th _ M th _
    ((snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ hφ.isoPullback.hom)]
  · simpa only [map_mul] using H
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd]; exact hs
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, Category.id_comp]
  · intro T _ y w
    rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc _ _ φ,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]

theorem exists_endomorphisms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z I M th sc p hvd hPF hfib => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨hrep, hsm, -, hp⟩ := hPF
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  have hsm' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have key : ∀ i : Option J, ∃ F : Z ⟶ Z, ∀ (K : Type) [Field K] (x : R →+* K) (f : pullback Z.hom (spMap x) ⟶ Z.left),
      (∃ (_ : IsAlgClosed K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left)
        (hφ : IsPullback φ t'.A.hom Z.hom (spMap x)), t'.Shape Mat κ ∧
        (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
        (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) ∧
        f = hφ.isoPullback.inv ≫ (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) →
      f = pullback.fst _ _ ≫ F.left := by
    intro i
    obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
    refine GlobalTheory.T.exists_family_morphism_from_veryDense_graphs R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d _
      hrep hrep hprop hprop hsm' ?_ ?_
    · rintro K _ x f ⟨_, t', φ, hφ, ht, ⟨σ, hE, hσ⟩, hl, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t' ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t'.A ⟶ t'.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · have e : spMap x ≫ spMap β = spMap (x.comp β) := by rw [← Spec.map_comp]; rfl
        clear hσ hl hφ φ
        generalize spMap x ≫ spMap β = s at e t' ht σ hE
        subst e
        exact fun p' q' f hf h => hQ K (x.comp β) t' σ p' q' f ht hf hE h
    · intro q r hq hr
      obtain ⟨P, ⟨K, _, _, x, t', hx, ht, hth⟩, hP⟩ := hvd q r hq hr
      obtain ⟨φ, hφ, hσ, -, hl⟩ := hfib K x t' ht hth
      exact ⟨P, ⟨K, _, x, _, hx, inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩, hP⟩
  choose F hF using key
  refine ⟨F, fun K _ _ x t' φ ht hfb i => ?_⟩
  obtain ⟨hφ, hσ, -, hl⟩ := hfb
  have := hF i K x _ ⟨inferInstance, t', φ, hφ, ht, hσ, hl, rfl⟩
  rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst_assoc] at this
  exact this.symm

end GlobalTheory.ZM.EndBuild
end
end
