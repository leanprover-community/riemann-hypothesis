import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClauses

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open Matrix

namespace GlobalTheory.ZarhinFam.KappaEx

def omegaB (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem omegaB_apply (h : ℕ) (a b : Fin h ⊕ Fin h → ℤ) : omegaB h a b = omegaStd a b := rfl

def emb (h : ℕ) (l : Fin 8) : Fin h ⊕ Fin h → Fin (8 * h) ⊕ Fin (8 * h) :=
  Sum.map (fun i => finProdFinEquiv (l, i)) (fun i => finProdFinEquiv (l, i))

def blk (h : ℕ) (l : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) where
  toFun a := a ∘ emb h l
  map_zero' := rfl
  map_add' _ _ := rfl

theorem omegaStd_eq_sum_blk (h : ℕ) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    omegaStd a b = ∑ l, omegaStd (blk h l a) (blk h l b) := by
  simp only [omegaStd]
  rw [← (finProdFinEquiv (m := 8) (n := h)).sum_comp, Fintype.sum_prod_type]
  rfl

def vMat (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (-(quat d)ᵀ) 0 1

theorem vMat_transpose_mul_form_mul {d : ℕ} (hd : 0 < d) : (vMat d)ᵀ * form d * vMat d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [vMat, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, quat_mul_transpose, h1, sub_smul]

theorem sum_sig {β : Type} [AddCommMonoid β] (g : Fin 4 ⊕ Fin 4 → β) : ∑ k, g (sig k) = ∑ s, g s := by
  simp [Fin.sum_univ_succ, Fintype.sum_sum_type, sig, add_assoc]

theorem sig_injective : Function.Injective sig := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [sig]

def kap (h d : ℕ) (k : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) :=
  ∑ l, vMat d (sig k) (sig l) • blk h l

theorem kap_apply (h d : ℕ) (k : Fin 8) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    kap h d k a = ∑ l, vMat d (sig k) (sig l) • blk h l a := by
  unfold kap
  rw [AddMonoidHom.finset_sum_apply]
  rfl

theorem inner_sum (d : ℕ) (m n : Fin 8) :
    ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) := by
  have e1 : ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ∑ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) :=
    sum_sig (fun p => ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n))
  have e2 : ∀ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) =
      ∑ q, vMat d p (sig m) * form d p q * vMat d q (sig n) :=
    fun p => sum_sig (fun q => vMat d p (sig m) * form d p q * vMat d q (sig n))
  rw [e1, Finset.sum_congr rfl fun p _ => e2 p]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem formZ_kap {h d : ℕ} (hd : 0 < d) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    formZ d h (fun k => kap h d k a) (fun k => kap h d k b) = omegaStd a b := by
  have e2 : ∀ k l, omegaStd (kap h d k a) (kap h d l b) =
      ∑ m, ∑ n, vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro k l
    rw [← omegaB_apply, kap_apply, kap_apply]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      omegaB_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [formZ, e2, Finset.mul_sum]
  have e3 : ∀ m n, ∑ k, ∑ l, form d (sig k) (sig l) *
      (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro m n
    rw [← inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ k, ∑ l, ∑ m, ∑ n, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b))
      = ∑ k, ∑ m, ∑ n, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
        simp only [e3]
    _ = omegaStd a b := by
        rw [vMat_transpose_mul_form_mul hd, omegaStd_eq_sum_blk]
        simp [Matrix.one_apply, sig_injective.eq_iff]

theorem blk_jlMap (h : ℕ) (l : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    blk h l (jlMap h a) = if l = 0 then a else 0 := by
  funext x
  split_ifs with hl
  · subst hl
    rcases x with i | i <;> simp [blk, emb, jlMap]
  · have hl1 : 1 ≤ (l : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hl (Fin.ext h0)
    rcases x with i | i <;> simp only [blk, emb, jlMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Sum.map_inl, Sum.map_inr, Pi.zero_apply] <;> rw [dif_neg] <;> simp only [finProdFinEquiv_apply_val, not_lt] <;>
      nlinarith [i.2]

theorem kap_jlMap (h d : ℕ) (k : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    kap h d k (jlMap h a) = if k = 0 then a else 0 := by
  rw [kap_apply]
  simp only [blk_jlMap, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases k <;> simp [vMat, sig]

end GlobalTheory.ZarhinFam.KappaEx

namespace GlobalTheory.ZarhinFam

open KappaEx in

theorem exists_kappaOK : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  intro h M d _ _ _ hd _
  refine ⟨kap h d, fun a b => ?_, fun a => ?_, fun k hk a => ?_⟩
  · rw [formZ_kap hd]
  · rw [kap_jlMap, if_pos rfl]
  · rw [kap_jlMap, if_neg hk]

end GlobalTheory.ZarhinFam
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinSymplecticTransfer : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  first | (exact @GlobalTheory.ZarhinFam.exists_kappaOK) | (exact GlobalTheory.ZarhinFam.exists_kappaOK) | (intros; apply GlobalTheory.ZarhinFam.exists_kappaOK  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomTorsionFree

open ReciprocityTheory.ChartRestriction.G.Out

theorem flat_surjective_mulA (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (d : ℕ) (hd : 1 ≤ d) : Flat (mulA B d).left ∧ Surjective (mulA B d).left := by
  have hc := hB.comm
  obtain ⟨hf, hfl⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S B hB d hd
  refine ⟨hfl, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hfin : IsFinite ((Over.pullback t).map (mulA B d)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hfin ⊢
  have hab := TLinPf.isAb_pullback t B hB
  have := hab.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hab _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ d) hfin).2

theorem eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  intro S A B _ _ _ _ _ hB d hd _ x y hx hy hxy
  obtain ⟨hfl, hsu⟩ := flat_surjective_mulA S B hB d hd
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (mulA B d)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, hxy]

end GlobalTheory.HomTorsionFree
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  first | (exact @GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (exact GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (intros; apply GlobalTheory.HomTorsionFree.eq_of_pow_eq  <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.Rig

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem pull_pull_lift {Y W X₁ X₂ : Over S} {M : LB (X₁ ⊗ X₂).left} (hM : M.IsLB) (u : Y ⟶ W) (f : W ⟶ X₁)
    (g : W ⟶ X₂) : CechPic.pull u.left (CechPic.pull (lift f g).left (cls M hM)) = evc hM (u ≫ f) (u ≫ g) := by
  rw [← pull_comp, ← Over.comp_left, comp_lift]; rfl

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (z z' : Y ⟶ Zob A B) :
    CechPic.pull (lift z z').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (z ≫ pa A B i) (z' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z ≫ pa A B i) (z' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z' ≫ pa A B i) (z ≫ pb A B j)) +
      ∑ j, evc hQ (z' ≫ pb A B j ≫ mu) (z ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, pull_pull_lift, lift_fst_assoc, lift_snd_assoc]

theorem zarhinBundle_pull_trivial_iff {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ)
    (mu : B ⟶ A) {Y : Over S} (u : Y ⟶ Zob A B ⊗ Zob A B) :
    (∃ t : ((zP A B hP hQ d mu).pull u.left).Gen, t.IsGen) ↔
      CechPic.pull u.left (zCls A B hP hQ d mu) = 0 := by
  rw [← cls_eq_zero_iff (pull_isLB (zarhinBundle_isLineBundle A B hP hQ d mu) _), cls_pull (zarhinBundle_isLineBundle A B hP hQ d mu), cls_zP]

theorem one_pa {Y : Over S} (i : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pa A B i = 1 := by
  simp [pa]

theorem one_pb {Y : Over S} (j : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pb A B j = 1 := by
  simp [pb]

theorem one_pb_assoc {Y X : Over S} (j : Fin 4) (f : B ⟶ X) : (1 : Y ⟶ Zob A B) ≫ pb A B j ≫ f = 1 ≫ f := by
  rw [← Category.assoc, one_pb]

end

section Sym
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem evc_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Y : Over S} (a a' : Y ⟶ A) : evc hP a a' = evc hP a' a := by
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) := (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hPs
  change CechPic.pull (lift a a').left (cls P hP) = _
  rw [e₁, pull_evc, lift_snd, lift_fst]

theorem evc_mu_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Q : LB (A ⊗ B).left} (hQ : IsDual A B Q) (hQ' : IsDual B A (swap Q)) {d : ℕ} {la : A ⟶ B} {mu : B ⟶ A}
    (hmu : IsMonHom mu) (hlm : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d)
    (hPQ : LBIso P (ev Q (fst A A) (snd A A ≫ la)))
    (htor : ∀ x y : B ⟶ A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y)
    {Y : Over S} (b b' : Y ⟶ B) : evc hQ.isLB (b' ≫ mu) b = evc hQ.isLB (b ≫ mu) b' := by
  have hQl := hQ.isLB
  have hs := hQ'.isLB
  have addL : ∀ (Y : Over S) (a a' : Y ⟶ A) (b : Y ⟶ B), evc hQl (a * a') b = evc hQl a b + evc hQl a' b :=
    (isAdditive_iff hQl).1 hQ.additive
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hQl a (b * b') = evc hQl a b + evc hQl a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 hQ'.additive Y b b' a
    rwa [evc_swap hQl hs, evc_swap hQl hs, evc_swap hQl hs] at k
  have powL : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl (a ^ n) b = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hQ.additive.evc_one hQl b
    | succ n ih => rw [pow_succ, addL, ih, succ_nsmul]
  have powR : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl a (b ^ n) = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQl hQ.zero a
    | succ n ih => rw [pow_succ, addR, ih, succ_nsmul]
  have PQ : ∀ (Y : Over S) (a a' : Y ⟶ A), evc hP a a' = evc hQl a (a' ≫ la) := by
    intro Y a a'
    have e₂ : cls P hP = evc hQl (fst A A) (snd A A ≫ la) := (CechPic.cls_eq_iff hP (pull_isLB hQl _)).2 hPQ
    change CechPic.pull (lift a a').left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]

  let Mb : LB (B ⊗ B).left := ev Q (fst B B ≫ mu) (snd B B)
  have hM : Mb.IsLB := pull_isLB hQl _
  have evcM : ∀ (Y : Over S) (b t : Y ⟶ B), evc hM b t = evc hQl (b ≫ mu) t := by
    intro Y b t
    rw [evc_ev hQl, lift_fst_assoc, lift_snd]
  have haM : IsAdditive Mb := (isAdditive_iff hM).2 fun Y b b' t => by
    rw [evcM, evcM, evcM, MonObj.mul_comp, addL]
  obtain ⟨x, hx, -⟩ := hQ'.univ B Mb hM haM
  have K : ∀ (Y : Over S) (b t : Y ⟶ B), evc hQl (b ≫ mu) t = evc hQl (t ≫ x) b := by
    intro Y b t
    have c := (CechPic.cls_eq_iff hM (pull_isLB hs _)).2 hx
    have k : evc hM b t = evc (pull_isLB hs _) b t := congrArg (CechPic.pull (lift b t).left) c
    rw [evc_ev hs, lift_fst, lift_snd_assoc, evc_swap hQl hs, evcM] at k
    exact k
  have hss : (swap (swap Q)).IsLB := pull_isLB hs _
  have ha' : IsAdditive (swap (swap Q)) := (isAdditive_iff hss).2 fun Y a a' t => by
    simp only [evc_swap hs hss, evc_swap hQl hs]; exact addL Y a a' t
  have hsM : (swap Mb).IsLB := pull_isLB hM _
  have haSM : IsAdditive (swap Mb) := (isAdditive_iff hsM).2 fun Y t t' b => by
    simp only [evc_swap hM hsM, evcM]; exact addR Y _ t t'
  have hxm : IsMonHom x := isMonHom_of_classifying S B B A Mb (swap Q) hQ' ha' hM haSM x hx
  have key : ∀ (Y : Over S) (b : Y ⟶ B) (a : Y ⟶ A), evc hQl (a ≫ la ≫ x) b = evc hQl (a ≫ la ≫ mu) b := by
    intro Y b a
    rw [← Category.assoc a la x, ← K, ← PQ, evc_symm hP hPs, PQ, Category.assoc, hml, hlm, comp_pow,
      Category.comp_id, comp_pow, Category.comp_id, powR, powL]
  have lx : la ≫ x = la ≫ mu := by
    apply hQ'.eq_of_evc
    rw [evc_swap hQl hs, evc_swap hQl hs, key]
  have xd : x ^ d = mu ^ d := by
    have e₁ : (𝟙 B ^ d) ≫ x = x ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    have e₂ : (𝟙 B ^ d) ≫ mu = mu ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    rw [← e₁, ← e₂, ← hml, Category.assoc, lx, ← Category.assoc]
  have xm : x = mu := htor x mu hxm hmu xd
  rw [K, xm]

end Sym

theorem zarhinBundle_rigidified_symmetric₂ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hdu _
  have hQ := hZ.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  refine ⟨(zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, (zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, ?_⟩
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_left c.isLB c.rig₁,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_right c.isLB c.rig₂,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
    refine (CechPic.cls_eq_iff hz (pull_isLB hz _)).1 ?_
    rw [cls_pull hz, cls_zP]
    conv_lhs => rw [← pull_id (zCls _ _ _ _ _ _), ← Over.id_left, ← lift_fst_snd]
    rw [pull_zCls, pull_zCls]
    have htor : ∀ x y : B ⟶ c.A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y :=
      GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq S c.A B c.ab hZ.1 d hd hdu
    have h1 : ∑ i, evc c.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) =
        ∑ i, evc c.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) :=
      Finset.sum_congr rfl fun i _ => evc_symm c.isLB c.symm _ _
    have h4 : ∑ j, evc hQ.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) =
        ∑ j, evc hQ.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) :=
      Finset.sum_congr rfl fun j _ => by
        simpa only [Category.assoc] using evc_mu_symm c.isLB c.symm hQ hZ.2.2.1 hZ.2.2.2.2.1 hZ.2.2.2.2.2.1
          hZ.2.2.2.2.2.2.1 hZ.2.2.2.2.2.2.2 htor (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j)
    rw [h1, h4]
    abel

end GlobalTheory.ZarhinFam.Rig
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_rigidified_symmetric : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  first | (exact @GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (exact GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (intros; apply GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrder_isRingAction_on_product : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (exact GlobalTheory.ZarhinFam.RAct.actZ_isRAct) | (intros; apply GlobalTheory.ZarhinFam.RAct.actZ_isRAct <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinOrderAction_rosati_adjoint : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Adj (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) (GlobalTheory.ZarhinFam.bar d) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  first | (exact @GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (exact GlobalTheory.ZarhinFam.AdjPf.adj_actZ) | (intros; apply GlobalTheory.ZarhinFam.AdjPf.adj_actZ <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinLevel_additive_killed_by_level : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (exact GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (intros; apply GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinProduct_relation_algebraic_clauses : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → IsMonHom (GlobalTheory.ZarhinFam.incZ c.A B) ∧ IsMonHom (GlobalTheory.ZarhinFam.prZ c.A B) ∧ GlobalTheory.ZarhinFam.incZ c.A B ≫ GlobalTheory.ZarhinFam.prZ c.A B = 𝟙 c.A ∧ GlobalTheory.ZarhinFam.prZ c.A B ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.idem d) ∧ ∀ a, c.lev a ≫ GlobalTheory.ZarhinFam.incZ c.A B = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (GlobalTheory.ZarhinFam.jlMap h a) := by
  first | (exact @GlobalTheory.ZarhinFam.zRel_alg) | (exact GlobalTheory.ZarhinFam.zRel_alg) | (intros; apply GlobalTheory.ZarhinFam.zRel_alg  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinFam

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (i : Fin 4) : incZ A B ≫ pa A B i = if i = 0 then 𝟙 A else 1 := by
  unfold incZ pa mkZ
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk A _) ⟨i⟩

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  unfold incZ pb mkZ
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk A _) ⟨j⟩
end

theorem zarhinBundle_pullback_inclusion : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hq0 : ∀ {Y : Over S} (a : Y ⟶ c.A), CechPic.pull (lift a (1 : Y ⟶ B)).left (cls Q hZ.2.1.isLB) = 0 :=
    fun a => evc_one_right hZ.2.1.isLB hZ.2.1.zero a
  have hp0 : ∀ {Y : Over S}, CechPic.pull (lift (1 : Y ⟶ c.A) (1 : Y ⟶ c.A)).left (cls c.P c.isLB) = 0 :=
    evc_one_left c.isLB c.rig₁ 1
  have hp1 : CechPic.pull (lift (fst c.A c.A) (snd c.A c.A)).left (cls c.P c.isLB) = cls c.P c.isLB := by
    rw [lift_fst_snd, Over.id_left, pull_id]
  refine (cls_eq_iff c.isLB (pull_isLB (zarhinBundle_isLineBundle _ _ _ _ _ _) _)).1 ?_
  rw [cls_pull (zarhinBundle_isLineBundle _ _ _ _ _ _), cls_zP]
  unfold zCls
  simp only [map_add, map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, tensorHom_fst_assoc,
    tensorHom_snd_assoc, incZ_pa, incZ_pb, Fin.sum_univ_four]
  simp only [MonObj.comp_one, Category.comp_id, ↓reduceIte, Fin.isValue, Fin.reduceEq, one_ne_zero, hq0, hp0, hp1, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end GlobalTheory.ZarhinFam
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end
