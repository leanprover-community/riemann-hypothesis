import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CupLeibniz
import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ConePairing
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight
import GroundTheory.ProfiniteCohomology.PoincarePairs.Devissage

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology

universe u

section Tuple

variable {α : Type*}

def consTuple {s m : ℕ} (h : s = m + 1) (a : α) (g : Fin m → α) : Fin s → α :=
  fun i => if hi : (i : ℕ) = 0 then a else g ⟨i - 1, by omega⟩

theorem consTuple_rfl {m : ℕ} (a : α) (g : Fin m → α) :
    consTuple (rfl : m + 1 = m + 1) a g = Fin.cons a g := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consTuple]
  · simp only [consTuple, Fin.val_succ, Nat.add_one_ne_zero, dite_false, Fin.cons_succ]
    congr 1

theorem continuous_consTuple [TopologicalSpace α] {s m : ℕ} (h : s = m + 1) (a : α) :
    Continuous (consTuple h a) := by
  refine continuous_pi fun i => ?_
  unfold consTuple
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

end Tuple

section Homotopy

variable {k F : Type u} [CommRing k] [Group F] [Fintype F] {X Y Z : Rep.{u} k F}
  (μ : X ⊗ Y ⟶ Z)

noncomputable def normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X) (y : (Fin s → F) → Y) : (Fin m → F) → Z :=
  fun g => ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F))))

theorem normHomotopyFun_add_left {s m : ℕ} (h : s = m + 1) (e e' : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (e + e') y = normHomotopyFun μ h e y + normHomotopyFun μ h e' y := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.add_tmul, map_add,
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_left {s m : ℕ} (h : s = m + 1) (c : k) (e : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (c • e) y = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

theorem normHomotopyFun_add_right {s m : ℕ} (h : s = m + 1) (e : X) (y y' : (Fin s → F) → Y) :
    normHomotopyFun μ h e (y + y') = normHomotopyFun μ h e y + normHomotopyFun μ h e y' := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.tmul_add, map_add,
    Finset.sum_add_distrib]

theorem normHomotopyFun_smul_right {s m : ℕ} (h : s = m + 1) (c : k) (e : X)
    (y : (Fin s → F) → Y) :
    normHomotopyFun μ h e (c • y) = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

theorem sum_ρ_μ_tmul_ρ_inv (e : X) (b : Y) :
    ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
  have h1 : ∀ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := fun a => by
    have h2 : ((X ⊗ Y).ρ a) ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F))) =
        ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
      change TensorProduct.map (X.ρ a) (Y.ρ a) (e ⊗ₜ[k] Y.ρ a⁻¹ b) = _
      rw [TensorProduct.map_tmul, Representation.self_inv_apply]
    exact (Rep.hom_comm_apply μ a _).symm.trans (congrArg _ h2)
  rw [Finset.sum_congr rfl fun a _ => h1 a, ← map_sum, ← TensorProduct.sum_tmul]
  congr 2
  simp [Representation.norm]

theorem normHomotopyFun_d_add {m : ℕ} (e : X) (y : (Fin (m + 1) → F) → Y) :
    (inhomogeneousCochains.d Z m).hom (normHomotopyFun μ rfl e y) +
        normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) := by
  funext g
  have hdy : ∀ a : F, (inhomogeneousCochains.d Y (m + 1)).hom y (Fin.cons a⁻¹ g) =
      Y.ρ a⁻¹ (y g) - y (Fin.cons (a⁻¹ * g 0) fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          y (Fin.cons a⁻¹ (Fin.contractNth j (· * ·) g)) := by
    intro a
    rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons,
      Fin.val_zero, Fin.val_succ, zero_add, pow_one, neg_one_smul]
    have e2 : ∀ j : Fin (m + 1), (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := fun _ => rfl
    simp only [e2]
    abel
  have hsplit : normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) g =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) -
        Z.ρ (g 0) (normHomotopyFun μ rfl e y fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          normHomotopyFun μ rfl e y (Fin.contractNth j (· * ·) g) := by
    simp only [normHomotopyFun, consTuple_rfl]
    simp only [hdy, TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, map_add, map_sub, map_sum, map_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [sum_ρ_μ_tmul_ρ_inv μ e (y g), Finset.sum_comm (β := Z.V)]
    congr 2
    · refine (Fintype.sum_equiv (Equiv.mulLeft (g 0)) _ _ fun a => ?_).symm
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]
    · funext j
      rw [Finset.smul_sum]
  rw [Pi.add_apply, inhomogeneousCochains.d_hom_apply, hsplit]
  have hpow : ∀ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) = -(-1 : k) ^ ((j : ℕ) + 1) :=
    fun j => by rw [pow_succ, mul_neg_one]
  simp only [hpow, neg_smul, Finset.sum_neg_distrib]
  abel

theorem normHomotopyFun_d_zero (e : X) (z : (Fin 0 → F) → Y) :
    normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y 0).hom z) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F))) -
        Z.ρ.norm (μ.hom ((e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F)))) := by
  funext g
  set b := z g with hb
  have hzc : z = fun _ => b := funext fun g' => congrArg z (Subsingleton.elim g' g)
  rw [hzc]
  simp only [normHomotopyFun, inhomogeneousCochains.d_hom_apply, consTuple_rfl, Fin.cons_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one,
    neg_one_smul, ← sub_eq_add_neg,
    TensorProduct.tmul_sub, map_sub, Finset.sum_sub_distrib]
  rw [sum_ρ_μ_tmul_ρ_inv]
  congr 1
  simp [Representation.norm]

end Homotopy

section LocallyConstant

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F] {X Y Z : Rep.{u} k F} [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z]
  (μ : X ⊗ Y ⟶ Z)

omit [IsTopologicalGroup F] [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z] in
theorem isLocallyConstant_normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X)
    {y : (Fin s → F) → Y} (hy : IsLocallyConstant y) :
    IsLocallyConstant (normHomotopyFun μ h e y) := by
  have e1 : normHomotopyFun μ h e y = ∑ a : F, fun g =>
      Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F)))) := by
    funext g
    simp [normHomotopyFun, Finset.sum_apply]
  rw [e1]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
    (IsLocallyConstant.const 0) fun a _ =>
      (hy.comp_continuous (continuous_consTuple h a⁻¹)).comp
        (fun b : Y => Z.ρ a (μ.hom ((e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))))

noncomputable def normHomotopy {s m : ℕ} (h : s = m + 1) :
    X →ₗ[k] (cochainsComplex Y).X s →ₗ[k] (cochainsComplex Z).X m :=
  LinearMap.mk₂ k (fun e y => mkCochain Z (normHomotopyFun μ h e (cochainOf Y y))
      (isLocallyConstant_normHomotopyFun μ h e (isLocallyConstant_cochainOf y)))
    (fun e e' _ => cochainOf_injective (normHomotopyFun_add_left μ h e e' _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_left μ h c e _))
    (fun e _ _ => cochainOf_injective (normHomotopyFun_add_right μ h e _ _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_right μ h c e _))

omit [IsDiscreteRep X] in
theorem cochainOf_normHomotopy {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochainsComplex Y).X s) :
    cochainOf Z (normHomotopy μ h e y) = normHomotopyFun μ h e (cochainOf Y y) :=
  rfl

omit [Fintype F] in

theorem cochainOf_cupPairingCochains_zeroCochain {n : ℕ} (x : X) (y : (cochainsComplex Y).X n)
    (g : Fin n → F) :
    cochainOf Z (cupPairingCochains μ (zero_add n) (zeroCochain X x) y) g =
      μ.hom ((x ⊗ₜ[k] cochainOf Y y g : (X ⊗ Y : Rep k F))) := by
  rw [cochainOf_cupPairingCochains]
  change μ.hom (GroupCoh.cupCochain _ _ _ g) = _
  rw [GroupCoh.cupCochain_apply]
  congr 2
  have hp : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  rw [hp, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  exact Fin.ext (zero_add _)

theorem d_normHomotopy_add {m : ℕ} (e : X) (y : (cochainsComplex Y).X (m + 1)) :
    ((cochainsComplex Z).d m (m + 1)).hom (normHomotopy μ rfl e y) +
        normHomotopy μ rfl e (((cochainsComplex Y).d (m + 1) (m + 1 + 1)).hom y) =
      cupPairingCochains μ (zero_add (m + 1)) (zeroCochain X (X.ρ.norm e)) y := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_d, cochainOf_normHomotopy, cochainOf_normHomotopy, cochainOf_d,
    normHomotopyFun_d_add]
  funext g
  rw [cochainOf_cupPairingCochains_zeroCochain]

theorem normHomotopy_d_zero (e : X) (z : (cochainsComplex Y).X 0) :
    normHomotopy μ rfl e (((cochainsComplex Y).d 0 1).hom z) =
      cupPairingCochains μ (zero_add 0) (zeroCochain X (X.ρ.norm e)) z -
        zeroCochain Z (Z.ρ.norm (μ.hom ((e ⊗ₜ[k] cochainOf Y z (fun i => i.elim0) :
          (X ⊗ Y : Rep k F))))) := by
  apply cochainOf_injective
  rw [cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_zero]
  funext g
  have hg : g = fun i => i.elim0 := Subsingleton.elim _ _
  subst hg
  rw [show ∀ a b : (cochainsComplex Z).X 0, cochainOf Z (a - b) = cochainOf Z a - cochainOf Z b
    from fun _ _ => rfl, Pi.sub_apply, cochainOf_cupPairingCochains_zeroCochain]
  rfl

end LocallyConstant

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Prod

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def prod (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) :
    LeibnizPairing (prodComplex M₁ M₂) (prodComplex N₁ N₂) (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N₁.X s × N₂.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y.1) (μ₂.leibniz h x.2 y.2)

theorem prod_μ_apply (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ}
    (h : r + s = n) (x : (prodComplex M₁ M₂).X r) (y : (prodComplex N₁ N₂).X s) :
    (prod μ₁ μ₂).μ h x y = ((μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2) : P₁.X n × P₂.X n) :=
  rfl

noncomputable def prodLeft (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) :
    LeibnizPairing (prodComplex M₁ M₂) N (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y, μ₂.μ h x.2 y)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y) (μ₂.leibniz h x.2 y)

theorem prodLeft_μ_apply (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) {r s n : ℕ}
    (h : r + s = n) (x : (prodComplex M₁ M₂).X r) (y : N.X s) :
    (prodLeft μ₁ μ₂).μ h x y = ((μ₁.μ h x.1 y, μ₂.μ h x.2 y) : P₁.X n × P₂.X n) :=
  rfl

end Prod

section DegZero

variable {E E' : ModuleCat.{u} k} {N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def degZeroμ (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    ∀ (r s n : ℕ), r + s = n →
      (degZeroComplex E).X r →ₗ[k] N.X s →ₗ[k] (degZeroComplex E').X n
  | 0, 0, 0, _ => β
  | _, _, _, _ => 0

theorem degZeroμ_succ (β : E →ₗ[k] N.X 0 →ₗ[k] E') (r s n : ℕ) (h : r + (s + 1) = n) :
    degZeroμ β r (s + 1) n h = 0 := by
  cases r <;> cases n <;> rfl

noncomputable def degZero (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    LeibnizPairing (degZeroComplex E) N (degZeroComplex E') where
  μ {r s n} h := degZeroμ β r s n h
  leibniz {r s n} h x y := by
    rw [degZeroComplex_d, degZeroComplex_d, degZeroμ_succ]
    simp

end DegZero

section CoconeHtpy

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (η : ∀ {r s n : ℕ}, r + s = n → K.X r →ₗ[k] N.X s →ₗ[k] shiftNegOneX L' n)

noncomputable def coconeLeftHtpyμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) :
        K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (p.2 + q.2) ((ρ.f s).hom z) + η h (p.1 + q.1) z = _
      rw [LinearMap.map_add₂, LinearMap.map_add₂]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h q.2 ((ρ.f s).hom z) + η h q.1 z)
      abel))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (c • p.2) ((ρ.f s).hom z) + η h (c • p.1) z = _
      rw [LinearMap.map_smul₂, LinearMap.map_smul₂]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) + η h p.1 (z + z') = _
      rw [map_add, map_add, map_add]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z') + η h p.1 z')
      abel))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) + η h p.1 (c • z) = _
      rw [map_smul, map_smul, map_smul]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))

theorem coconeLeftHtpyμ_apply {r s n : ℕ} (h : r + s = n) (x : K.X r) (y : shiftNegOneX L r)
    (z : N.X s) :
    coconeLeftHtpyμ μL ρ μK η (f := f) (f' := f') h ((x, y) : K.X r × shiftNegOneX L r) z =
      ((μK.μ h x z, μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) :
        K'.X n × shiftNegOneX L' n) :=
  rfl

noncomputable def coconeLeftHtpy
    (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
      shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
        shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
          η (by omega) ((K.d r (r + 1)).hom x) z +
          (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftHtpyμ μL ρ μK η h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) =
      (μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        η (by omega) ((K.d r (r + 1)).hom x) z) +
        (-1 : k) ^ r • (μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z)) + η (by omega) x ((N.d s (s + 1)).hom z))
    have key := eq_sub_of_add_eq' (hη h x z)
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, map_add, key,
      shiftLeft_leibniz, LinearMap.map_add₂, shiftLeft_succ, smul_add]
    abel

variable (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
    shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
      η (by omega) ((K.d r (r + 1)).hom x) z +
      (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z))

theorem coconeLeftHtpy_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeftHtpy μL ρ μK η hη).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
      (mappingCoconeNat.homologyδ f' n).hom
        (μL.homology h ξ ((HomologicalComplex.homologyMap ρ s).hom z)) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ r ξ
  obtain ⟨w, rfl⟩ := homologyπ_hom_surjective _ s z
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f r c
  rw [homologyMap_homologyπ_apply, homology_homologyπ]
  obtain ⟨c'', hc''1, hc''2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' n
    (μL.cycles h c ((HomologicalComplex.cyclesMap ρ s).hom w))
  rw [hc'1, hc''1, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cycles, hc'2, hc''2, iCycles_cycles, iCycles_cyclesMap_apply]
  refine Prod.ext (LinearMap.map_zero₂ _ _) ?_
  change μL.shiftLeft (r + 1) s (n + 1) h' _ _ + η h' 0 _ = _
  rw [LinearMap.map_zero₂, add_zero]
  rfl

end CoconeHtpy

end LeibnizPairing

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Pairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}

variable (B) in

noncomputable def tateLocalResB :
    cochainsComplex B ⟶ tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B)
      (fun w => Rep.res (ψ w).toMonoidHom B) :=
  prodLift (localRes φ B _ fun _ => 𝟙 _) (localRes ψ B _ fun _ => 𝟙 _)

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)

noncomputable def zeroCochainValue : (cochainsComplex B).X 0 →ₗ[k] B where
  toFun z := cochainOf B z (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def tateExtraPairingAt (w : κ) : Aᵣ w →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] Cᵣ w :=
  ((TensorProduct.mk k (Aᵣ w) (Rep.res (ψ w).toMonoidHom B)).compr₂ (μᵣ w).hom.toLinearMap).compl₂
    (zeroCochainValue (B := B))

noncomputable def tateExtraPairing :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] (∀ w, Cᵣ w) :=
  LinearMap.mk₂ k (fun e z w => tateExtraPairingAt ψ μᵣ w (e w) z)
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => map_add (tateExtraPairingAt ψ μᵣ w _) _ _)
    (fun _ _ _ => funext fun w => map_smul (tateExtraPairingAt ψ μᵣ w _) _ _)

omit [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] [∀ w, IsDiscreteRep (Aᵣ w)]
  [∀ w, IsDiscreteRep (Cᵣ w)] in
theorem tateExtraPairing_apply (e : ∀ w, Aᵣ w) (z : (cochainsComplex B).X 0) (w : κ) :
    tateExtraPairing ψ μᵣ e z w = (μᵣ w).hom ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
      (Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B : Rep k (F w)))) :=
  rfl

noncomputable def tateGlobalCup :
    LeibnizPairing (tateGlobalComplex A Aᵣ) (cochainsComplex B) (tateGlobalComplex C Cᵣ) :=
  LeibnizPairing.prodLeft (cupLeibniz μ) (LeibnizPairing.degZero (tateExtraPairing ψ μᵣ))

noncomputable def tateLocalCup :
    LeibnizPairing (tateLocalComplex Aᵥ Aᵣ)
      (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B) (fun w => Rep.res (ψ w).toMonoidHom B))
      (tateLocalComplex Cᵥ Cᵣ) :=
  LeibnizPairing.prod (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w))

noncomputable def tateNormHomotopy {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (∀ w, (cochainsComplex (Cᵣ w)).X m) :=
  LinearMap.mk₂ k (fun e z w => normHomotopy (μᵣ w) h (e w)
      (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f s).hom z w))
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun e _ _ => funext fun w => by
      rw [map_add]
      exact map_add (normHomotopy (μᵣ w) h (e w)) _ _)
    (fun c e _ => funext fun w => by
      rw [map_smul]
      exact map_smul (normHomotopy (μᵣ w) h (e w)) c _)

noncomputable def tateCupHomotopyL {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (tateLocalComplex Cᵥ Cᵣ).X m :=
  -(tateNormHomotopy ψ μᵣ h).compr₂ (LinearMap.inr k
    ((piComplex fun v => cochainsComplex (Cᵥ v)).X m) ((piComplex fun w => cochainsComplex (Cᵣ w)).X m))

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopyL_apply {s m : ℕ} (h : s = m + 1) (e : ∀ w, Aᵣ w)
    (z : (cochainsComplex B).X s) :
    tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) h e z = ((0, -tateNormHomotopy ψ μᵣ h e z) :
        (piComplex fun v => cochainsComplex (Cᵥ v)).X m ×
          (piComplex fun w => cochainsComplex (Cᵣ w)).X m) :=
  Prod.ext neg_zero rfl

noncomputable def tateCupHomotopy : ∀ (r s n : ℕ), r + s = n →
    (tateGlobalComplex A Aᵣ).X r →ₗ[k] (cochainsComplex B).X s →ₗ[k]
      shiftNegOneX (tateLocalComplex Cᵥ Cᵣ) n
  | 0, _, n + 1, h => (tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) (by omega : _ = n + 1)).comp
      (LinearMap.snd k _ ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0))
  | _, _, _, _ => 0

end Pairing

section Spec

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

theorem normCochains_f_succ_apply' (n : ℕ) (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X (n + 1)) :
    ((normCochains Aᵣ).f (n + 1)).hom e = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_succ_left (r s n : ℕ) (h : r + 1 + s = n) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) (r + 1) s n h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_zero (s : ℕ) (h : 0 + s = 0) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) 0 s 0 h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_succ (s n : ℕ) (h : 0 + s = n + 1) (hs : s = n + 1)
    (x : (tateGlobalComplex A Aᵣ).X 0) (z : (cochainsComplex B).X s) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) 0 s (n + 1) h x z =
      tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) hs x.2 z :=
  rfl

include hμ hμr in

theorem tateCupHomotopy_spec {r s n : ℕ} (h : r + s = n) (x : (tateGlobalComplex A Aᵣ).X r)
    (z : (cochainsComplex B).X s) :
    shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n (((tateCompactRes φ ψ C Cᵥ c Cᵣ cr).f n).hom
        ((tateGlobalCup ψ μ μᵣ).μ h x z)) +
        (shiftNegOneD (tateLocalComplex Cᵥ Cᵣ) n).hom (tateCupHomotopy ψ μᵣ r s n h x z) =
      shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n ((tateLocalCup φ ψ μᵥ μᵣ).μ h
          (((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f r).hom x) (((tateLocalResB φ ψ B).f s).hom z)) +
        tateCupHomotopy ψ μᵣ (r + 1) s (n + 1) (by omega)
          (((tateGlobalComplex A Aᵣ).d r (r + 1)).hom x) z +
        (-1 : k) ^ r • tateCupHomotopy ψ μᵣ r (s + 1) (n + 1) (by omega) x
          (((cochainsComplex B).d s (s + 1)).hom z) := by
  rcases r with _ | r
  · rcases s with _ | t
    ·
      obtain rfl : n = 0 := by omega
      rw [tateCupHomotopy_zero_zero, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ 1 0 _ rfl, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply]
      erw [tateCupHomotopyL_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f 0).hom (cupPairingCochains μ h x.1 z) =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f 0).hom z) + 0
        rw [add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f 0).hom (cupPairingCochains μ h x.1 z) w +
            zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm (tateExtraPairing ψ μᵣ (show ∀ w, Aᵣ w from x.2) z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f 0).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (0 + 1)).hom (((cochainsComplex B).d 0 (0 + 1)).hom z) w)
        have hres := congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (0 + 1)).hom
            (((cochainsComplex B).d 0 (0 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d 0 (0 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ 0 _ w
        have hz0 : cochainOf (Rep.res (ψ w).toMonoidHom B)
            (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w)
            (fun i => i.elim0) = cochainOf B z (fun i => i.elim0) :=
          congrArg (cochainOf B z) (Subsingleton.elim _ _)
        rw [hres, LinearMap.map_add₂, hd, normHomotopy_d_zero, hz0]
        change _ + zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm ((μᵣ w).hom _)) = _
        abel
    ·
      obtain rfl : n = t + 1 := by omega
      rw [tateCupHomotopy_zero_succ ψ μᵣ (t + 1) t _ rfl, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ (t + 1 + 1) (t + 1) _ rfl, LinearMap.zero_apply,
        LinearMap.zero_apply, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
      erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply, prodComplex_d_hom_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f (t + 1)).hom (cupPairingCochains μ h x.1 z) +
            -((piComplex fun v => cochainsComplex (Cᵥ v)).d t (t + 1)).hom 0 =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f (t + 1)).hom z) + 0
        rw [map_zero, neg_zero, add_zero, add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -(((piComplex fun w => cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-tateNormHomotopy ψ μᵣ (rfl : t + 1 = t + 1) x.2 z) w) = _
        erw [piComplex_d_hom_apply]
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -((cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
                (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1 + 1)).hom
              (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w)
        have hres : ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w =
            cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w)
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w) :=
          congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
            (t + 1 + 1)).hom (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d (t + 1) (t + 1 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
                (t + 1)).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ (t + 1) _ w
        have key := d_normHomotopy_add (μᵣ w) ((show ∀ w, Aᵣ w from x.2) w)
          (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        rw [hres, LinearMap.map_add₂, hd, map_neg, neg_neg, ← key]
        change _ + (0 : (cochainsComplex (Cᵣ w)).X (t + 1)) + _ = _
        abel
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    rw [tateCupHomotopy_succ_left, tateCupHomotopy_succ_left, tateCupHomotopy_succ_left,
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero, smul_zero, add_zero,
      shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    refine Prod.ext ?_ ?_
    · exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
    · change ((localRes ψ C Cᵣ cr).f (m + 1)).hom (cupPairingCochains μ h x.1 z) +
          ((normCochains Cᵣ).f (m + 1)).hom
            (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) (r + 1) s (m + 1) h x.2 z) =
        (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w)).μ h
          (((localRes ψ A Aᵣ ar).f (r + 1)).hom x.1 + ((normCochains Aᵣ).f (r + 1)).hom x.2)
          (((localRes ψ B _ fun _ => 𝟙 _).f s).hom z)
      rw [normCochains_f_succ_apply', normCochains_f_succ_apply', add_zero, add_zero]
      exact localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z

end Spec

section ProdHomology

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_prodFst_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodFst P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₁.homology h ((HomologicalComplex.homologyMap (prodFst M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodFst N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

theorem LeibnizPairing.homologyMap_prodSnd_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodSnd P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap (prodSnd M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodSnd N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

end ProdHomology

section Cup

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

noncomputable def tateCompactCupLeibniz :
    LeibnizPairing (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar) (cochainsComplex B)
      (tateCompactCochains φ ψ C Cᵥ c Cᵣ cr) :=
  LeibnizPairing.coconeLeftHtpy (tateLocalCup φ ψ μᵥ μᵣ) (tateLocalResB φ ψ B)
    (tateGlobalCup ψ μ μᵣ) (fun {r s n} h => tateCupHomotopy ψ μᵣ r s n h)
    (fun h x z => tateCupHomotopy_spec φ ψ μ μᵥ μᵣ hμ hμr h x z)

noncomputable def tateCompactCup {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar r →ₗ[k] cohomology B s →ₗ[k]
      tateCompactCohomology φ ψ C Cᵥ c Cᵣ cr n :=
  (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h

theorem tateCompactCup_tateLocalToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : (∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) (z : cohomology B s) :
    tateCompactCup φ ψ μ μᵥ μᵣ hμ hμr h' ((tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar r).hom ξ) z =
      (tateLocalToCompact φ ψ C Cᵥ c Cᵣ cr n).hom
        ((fun v => cupPairing (μᵥ v) h (ξ.1 v)
            ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) s).hom z)),
          (fun w => cupPairing (μᵣ w) h (ξ.2 w)
            ((cohomologyMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w)) (𝟙 _) s).hom z))) := by
  change (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h'
      ((mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) r).hom
        ((tateLocalCohomologyIso Aᵥ Aᵣ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (tateCompactRes φ ψ C Cᵥ c Cᵣ cr) n).hom
      ((tateLocalCohomologyIso Cᵥ Cᵣ n).inv.hom _)
  refine (LeibnizPairing.coconeLeftHtpy_homology_homologyδ _ _ _ _ _ h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (tateLocalCohomologyIso Cᵥ Cᵣ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Cᵥ Cᵣ n).inv_hom_id]
  have hξ := hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Aᵥ Aᵣ r).inv_hom_id
    (show ModuleCat.of k ((∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) from ξ)
  rw [tateLocalCohomologyIso_hom_apply] at hξ
  rw [tateLocalCohomologyIso_hom_apply]
  have ρ1 : tateLocalResB φ ψ B ≫ prodFst _ _ =
      localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodFst _ _
  have ρ2 : tateLocalResB φ ψ B ≫ prodSnd _ _ =
      localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodSnd _ _
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodFst_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
    refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵥ v) h p q) (congrFun (congrArg Prod.fst hξ) v) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodFst _ _) s).symm z, ρ1]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 (Rep.res (φ v).toMonoidHom B))) s) z) v
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodSnd_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun w => cupLeibniz (μᵣ w)) h _ _ w).trans ?_
    refine (cupLeibniz_homology (μᵣ w) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵣ w) h p q) (congrFun (congrArg Prod.snd hξ) w) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodSnd _ _) s).symm z, ρ2]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun w => cochainsMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w))
        (𝟙 (Rep.res (ψ w).toMonoidHom B))) s) z) w

end Cup

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Compat

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F]

theorem normHomotopy_compat_left {X₁ X₂ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁] [IsDiscreteRep Y₂]
    [IsDiscreteRep Z] (μ₁ : X₁ ⊗ Y₁ ⟶ Z) (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (f : X₁ ⟶ X₂) (g : Y₂ ⟶ Y₁)
    (hc : (f ⊗ₘ 𝟙 Y₂) ≫ μ₂ = (𝟙 X₁ ⊗ₘ g) ≫ μ₁) {s m : ℕ} (h : s = m + 1) (e : X₁)
    (y : (cochainsComplex Y₂).X s) :
    normHomotopy μ₂ h (f.hom e) y = normHomotopy μ₁ h e (((cochainsMap g).f s).hom y) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₁ ⊗ Y₂ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₂ y (consTuple h a⁻¹ σ) :
    (X₁ ⊗ Y₂ : Rep k F)))) hc

theorem normHomotopy_compat_right {X₂ X₃ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁]
    [IsDiscreteRep Y₂] [IsDiscreteRep Z] (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (μ₃ : X₃ ⊗ Y₁ ⟶ Z) (f : Y₁ ⟶ Y₂)
    (g : X₂ ⟶ X₃) (hc : (𝟙 X₂ ⊗ₘ f) ≫ μ₂ = (g ⊗ₘ 𝟙 Y₁) ≫ μ₃) {s m : ℕ} (h : s = m + 1) (e : X₂)
    (y : (cochainsComplex Y₁).X s) :
    normHomotopy μ₂ h e (((cochainsMap f).f s).hom y) = normHomotopy μ₃ h (g.hom e) y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₂ ⊗ Y₁ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₁ y (consTuple h a⁻¹ σ) :
    (X₂ ⊗ Y₁ : Rep k F)))) hc

end Compat

section TwoSequences

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {SA : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SA.X₁] [IsDiscreteRep SA.X₂]
  [IsDiscreteRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsDiscreteRep (SAᵥ v).X₁] [∀ v, IsDiscreteRep (SAᵥ v).X₂] [∀ v, IsDiscreteRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ SAᵥ v)
  {SAᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))}
  [∀ w, IsDiscreteRep (SAᵣ w).X₁] [∀ w, IsDiscreteRep (SAᵣ w).X₂] [∀ w, IsDiscreteRep (SAᵣ w).X₃]
  (sAr : ∀ w, SA.map (Rep.resFunctor (ψ w).toMonoidHom) ⟶ SAᵣ w)
  {SB : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SB.X₁] [IsDiscreteRep SB.X₂]
  [IsDiscreteRep SB.X₃] {C : Rep.{u} k G} [IsDiscreteRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsDiscreteRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Cᵣ w)]
  {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v).toMonoidHom SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v).toMonoidHom SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v).toMonoidHom SB.X₁ ⟶ Cᵥ v)
  (μ₁ᵣ : ∀ w, (SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₃ ⟶ Cᵣ w)
  (μ₂ᵣ : ∀ w, (SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ ⟶ Cᵣ w)
  (μ₃ᵣ : ∀ w, (SAᵣ w).X₃ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ ⟶ Cᵣ w)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₃ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)
  (hμ₁ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₁ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₁ (𝟙 _) ≫ μ₁ᵣ w)
  (hμ₂ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₂ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₂ (𝟙 _) ≫ μ₂ᵣ w)
  (hμ₃ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₃ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₃ (𝟙 _) ≫ μ₃ᵣ w)

include hμ₂ hμ₂ᵣ in

theorem tateCompactCup_tateCompactδ_add_tateCompactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (h₁₂ᵣ : ∀ w, ((SAᵣ w).f ⊗ₘ 𝟙 _) ≫ μ₂ᵣ w =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.g) ≫ μ₁ᵣ w)
    (h₂₃ᵣ : ∀ w, (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.f) ≫ μ₂ᵣ w =
      ((SAᵣ w).g ⊗ₘ 𝟙 _) ≫ μ₃ᵣ w)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSAᵣ : ∀ w, (SAᵣ w).ShortExact)
    (hSB : SB.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : tateCompactCohomology φ ψ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃)
      (fun w => (SAᵣ w).X₃) (fun w => (sAr w).τ₃) r)
    (y : cohomology SB.X₃ s) :
    tateCompactCup φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ h₁ ((tateCompactδ φ ψ sA sAr hSA hSAᵥ hSAᵣ r).hom x) y +
      (-1 : k) ^ r • tateCompactCup φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ SA SAᵥ sA SAᵣ sAr))
    (SN := cochainsShortComplex SB) (tateCompactCupLeibniz φ ψ μ₂ μ₂ᵥ μ₂ᵣ hμ₂ hμ₂ᵣ)
    (tateCompactCupLeibniz φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ) (tateCompactCupLeibniz φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ)
    ?_ ?_ (tateCompactCochains_shortExact φ ψ sA sAr hSA hSAᵥ hSAᵣ)
    (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₁ fun w => (SAᵣ w).X₁).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₁) fun w => (SAᵣ w).X₁) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₂ y (fun i => i.elim0) :
            ((SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ : Rep k (F w))))) (h₁₂ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).f).hom e) y =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₁ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.g).f (t + 1)).hom y)
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_left (μ₁ᵣ w) (μ₂ᵣ w) (SAᵣ w).f _ (h₁₂ᵣ w) rfl (e w) _
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).f) fun w => (SAᵣ w).f).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₂).f s).hom y) + 0 =
            (tateLocalCup φ ψ μ₁ᵥ μ₁ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₃).f s).hom (((cochainsMap SB.g).f s).hom y)) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₁ᵣ w) (μ₂ᵣ w) (h₁₂ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₂ y (⇑(ψ w).toMonoidHom ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₂ fun w => (SAᵣ w).X₂).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₂) fun w => (SAᵣ w).X₂) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₁ y (fun i => i.elim0) :
            ((SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ : Rep k (F w))))) (h₂₃ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.f).f (t + 1)).hom y) =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₃ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).g).hom e) y
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_right (μ₂ᵣ w) (μ₃ᵣ w)
            ((Rep.resFunctor (ψ w).toMonoidHom).map SB.f) (SAᵣ w).g (h₂₃ᵣ w) rfl (e w)
            (((localRes ψ SB.X₁ (fun w => Rep.res (ψ w).toMonoidHom SB.X₁) fun _ => 𝟙 _).f
              (t + 1)).hom y w)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₂).f s).hom (((cochainsMap SB.f).f s).hom y)) + 0 =
            (tateLocalCup φ ψ μ₃ᵥ μ₃ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).g) fun w => (SAᵣ w).g).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₁).f s).hom y) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₂ᵣ w) (μ₃ᵣ w) (h₂₃ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₁ y (⇑(ψ w).toMonoidHom ∘ τ)) σ

end TwoSequences

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance 2000] Rep.hV2

section ResMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

noncomputable abbrev tateCompactCochainsResMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (g : A ⟶ B) :
    tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _) ⟶
      tateCompactCochains φ ψ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom B) (fun _ => 𝟙 _) :=
  tateCompactCochainsMap φ ψ (Aᵥ := fun v => Rep.res (φ v).toMonoidHom A)
    (Bᵥ := fun v => Rep.res (φ v).toMonoidHom B) (Aᵣ := fun w => Rep.res (ψ w).toMonoidHom A)
    (Bᵣ := fun w => Rep.res (ψ w).toMonoidHom B) g
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)

noncomputable abbrev tateCompactCohomologyResMap {A B : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep B] (g : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyRes φ ψ A n ⟶ tateCompactCohomologyRes φ ψ B n :=
  HomologicalComplex.homologyMap (tateCompactCochainsResMap φ ψ g) n

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

theorem tateCompactCochainsResMap_add (g₁ g₂ : A ⟶ B) :
    tateCompactCochainsResMap φ ψ (g₁ + g₂) =
      tateCompactCochainsResMap φ ψ g₁ + tateCompactCochainsResMap φ ψ g₂ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_add g₁ g₂)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v)) (cochainsMap_add
          ((Rep.resFunctor (φ v).toMonoidHom).map g₁) ((Rep.resFunctor (φ v).toMonoidHom).map g₂))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w)) (cochainsMap_add
          ((Rep.resFunctor (ψ w).toMonoidHom).map g₁) ((Rep.resFunctor (ψ w).toMonoidHom).map g₂))

theorem tateCompactCochainsResMap_zero :
    tateCompactCochainsResMap φ ψ (0 : A ⟶ B) = 0 := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_zero (A := A) (B := B))
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v))
          (cochainsMap_zero (A := Rep.res (φ v).toMonoidHom A) (B := Rep.res (φ v).toMonoidHom B))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w))
          (cochainsMap_zero (A := Rep.res (ψ w).toMonoidHom A) (B := Rep.res (ψ w).toMonoidHom B))

theorem tateCompactCochainsResMap_id : tateCompactCochainsResMap φ ψ (𝟙 A) = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

theorem tateCompactCochainsResMap_comp (g : A ⟶ B) (g' : B ⟶ C) :
    tateCompactCochainsResMap φ ψ (g ≫ g') =
      tateCompactCochainsResMap φ ψ g ≫ tateCompactCochainsResMap φ ψ g' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w).toMonoidHom A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v).toMonoidHom A) fun w => Rep.res (ψ w).toMonoidHom A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

theorem tateCompactCohomologyResMap_add (g₁ g₂ : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g₁ + g₂) n =
      tateCompactCohomologyResMap φ ψ g₁ n + tateCompactCohomologyResMap φ ψ g₂ n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_add,
    HomologicalComplex.homologyMap_add]
  rfl

theorem tateCompactCohomologyResMap_zero (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (0 : A ⟶ B) n = 0 := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_zero,
    HomologicalComplex.homologyMap_zero]
  rfl

theorem tateCompactCohomologyResMap_id (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (𝟙 A) n = 𝟙 _ := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_id,
    HomologicalComplex.homologyMap_id]
  rfl

theorem tateCompactCohomologyResMap_comp (g : A ⟶ B) (g' : B ⟶ C) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g ≫ g') n =
      tateCompactCohomologyResMap φ ψ g n ≫ tateCompactCohomologyResMap φ ψ g' n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

theorem tateCompactCohomologyResMap_finsetSum {J : Type*} (s : Finset J) (f : J → (A ⟶ B))
    (m : ℕ) :
    tateCompactCohomologyResMap φ ψ (∑ j ∈ s, f j) m =
      ∑ j ∈ s, tateCompactCohomologyResMap φ ψ (f j) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [tateCompactCohomologyResMap_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tateCompactCohomologyResMap_add, ih]

theorem nsmul_tateCompactCohomologyRes_eq_zero {m : ℕ} (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : tateCompactCohomologyRes φ ψ A n) : m • x = 0 := by
  have h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0 := by
    rw [Finset.sum_const, Finset.card_range]
    ext a
    exact hm a
  have e : (tateCompactCohomologyResMap φ ψ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x =
      (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom x := by rw [h0]
  rw [tateCompactCohomologyResMap_finsetSum, tateCompactCohomologyResMap_zero] at e
  simp only [tateCompactCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e
  simpa using e

end ResMap

section Sequence

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃]

noncomputable def tateCompactδRes (hS : S.ShortExact) (n : ℕ) :
    tateCompactCohomologyRes φ ψ S.X₃ n ⟶ tateCompactCohomologyRes φ ψ S.X₁ (n + 1) :=
  tateCompactδ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
    (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

variable (hS : S.ShortExact)

include hS in

theorem tateCompactRes_exact₂ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.f n) (tateCompactCohomologyResMap φ ψ S.g n)
      (by rw [← tateCompactCohomologyResMap_comp, S.zero, tateCompactCohomologyResMap_zero])).Exact :=
  tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

theorem tateCompactRes_exact₃ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.g n) (tateCompactδRes φ ψ hS n)
      (tateCompactCohomologyMap₂₃_tateCompactδ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
        (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n)).Exact :=
  tateCompactCohomology_exact₃ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

theorem tateCompactRes_exact₁ (n : ℕ) :
    (ShortComplex.mk (tateCompactδRes φ ψ hS n) (tateCompactCohomologyResMap φ ψ S.f (n + 1))
      (tateCompactδ_tateCompactCohomologyMap₁₂ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom)) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
        (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n)).Exact :=
  tateCompactCohomology_exact₁ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w).toMonoidHom)) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hS)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hS) n

end Sequence

section CupRes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

noncomputable def tateCompactCupRes {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomologyRes φ ψ A r →ₗ[k] cohomology B s →ₗ[k] tateCompactCohomologyRes φ ψ C n :=
  tateCompactCup φ ψ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom μ) h

def tateCompactDualityMap (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] :
    cohomology M r →+ (tateCompactCohomologyRes φ ψ (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp ((bilinAddHom (tateCompactCupRes φ ψ (dualEvalPairing D M)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem tateCompactDualityMap_apply (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ}
    (h : r + s = m) (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G)
    [IsDiscreteRep M] [IsDiscreteRep (dualRep D M)] (x : cohomology M r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D M) s) :
    tateCompactDualityMap φ ψ D h t M x y =
      t (tateCompactCupRes φ ψ (dualEvalPairing D M) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end CupRes

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

structure TateCompactDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep D] (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) :
    Prop where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (tateCompactCohomologyRes φ ψ M 4)

  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))

end Hypotheses

end GroundTheory.ProfCoh
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Limits GroundTheory.GroupCoh

universe u

attribute [local instance 2000] Rep.hV2

section CupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A A' B B' C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B]
  [IsDiscreteRep B'] [IsDiscreteRep C]

noncomputable abbrev tateCompactCupResLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (tateCompactCochains φ ψ A (fun v => Rep.res (φ v).toMonoidHom A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom A) (fun _ => 𝟙 _)) (cochainsComplex B)
      (tateCompactCochains φ ψ C (fun v => Rep.res (φ v).toMonoidHom C) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w).toMonoidHom C) (fun _ => 𝟙 _)) :=
  tateCompactCupLeibniz φ ψ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom μ)

theorem tateCompactCupRes_eq_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCupRes φ ψ μ h = (tateCompactCupResLeibniz φ ψ μ).homology h :=
  rfl

theorem tateCompactCupResLeibniz_naturality (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C) (g : A' ⟶ A)
    (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A' (fun v => Rep.res (φ v).toMonoidHom A') (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w).toMonoidHom A') (fun _ => 𝟙 _)).X r)
    (z : (cochainsComplex B).X s) :
    (tateCompactCupResLeibniz φ ψ μ).μ h (((tateCompactCochainsResMap φ ψ g).f r).hom p) z =
      (tateCompactCupResLeibniz φ ψ μ').μ h p (((cochainsMap f).f s).hom z) := by
  revert p
  intro (p : (tateGlobalComplex A' fun w => Rep.res (ψ w).toMonoidHom A').X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom A')
      fun w => Rep.res (ψ w).toMonoidHom A') r)
  obtain ⟨⟨x0, e⟩, b⟩ := p
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply cochainOf_injective
    funext σ
    exact (cupCochain_naturality μ μ' g f hμ h (cochainOf _ x0) (cochainOf _ z) σ).symm
  · rcases r with _ | r
    · rcases s with _ | s
      · obtain rfl : n = 0 := by omega
        funext w
        exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
          (Rep.res (ψ w).toMonoidHom A' ⊗ Rep.res (ψ w).toMonoidHom B : Rep k (F w)))))
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ)
      · rfl
    · rfl
  · rcases r with _ | r
    · rcases s with _ | t
      · obtain rfl : n = 0 := by omega
        exact Subsingleton.elim (α := PUnit) _ _
      · obtain rfl : n = t + 1 := by omega
        change (0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C)
              fun w => Rep.res (ψ w).toMonoidHom C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (rfl : t + 1 = t + 1)
              ((piRepHom fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g).hom e) z =
          (0 : (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom C)
              fun w => Rep.res (ψ w).toMonoidHom C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ')
              (Cᵥ := fun v => Rep.res (φ v).toMonoidHom C) (rfl : t + 1 = t + 1) e
              (((cochainsMap f).f (t + 1)).hom z)
        erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
        refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
        have key := normHomotopy_compat_left ((Rep.resFunctor (ψ w).toMonoidHom).map μ')
          ((Rep.resFunctor (ψ w).toMonoidHom).map μ) ((Rep.resFunctor (ψ w).toMonoidHom).map g)
          ((Rep.resFunctor (ψ w).toMonoidHom).map f)
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ) (rfl : t + 1 = t + 1) (e w)
          (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        exact key
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      change (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ)).μ (show r + s = m by omega)
            ((tateLocalMap (fun v => (Rep.resFunctor (φ v).toMonoidHom).map g)
              fun w => (Rep.resFunctor (ψ w).toMonoidHom).map g).f r |>.hom b)
            (((tateLocalResB φ ψ B).f s).hom z) + 0 =
          (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ')
            (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map μ')).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B').f s).hom (((cochainsMap f).f s).hom z)) + 0
      rw [add_zero, add_zero]
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (φ v).toMonoidHom).map μ)
          ((Rep.resFunctor (φ v).toMonoidHom).map μ') ((Rep.resFunctor (φ v).toMonoidHom).map g)
          ((Rep.resFunctor (φ v).toMonoidHom).map f)
          (resFunctor_map_naturality (φ v).toMonoidHom μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.1 v)) (fun τ => cochainOf B z (⇑(φ v).toMonoidHom ∘ τ)) σ).symm
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (ψ w).toMonoidHom).map μ)
          ((Rep.resFunctor (ψ w).toMonoidHom).map μ') ((Rep.resFunctor (ψ w).toMonoidHom).map g)
          ((Rep.resFunctor (ψ w).toMonoidHom).map f)
          (resFunctor_map_naturality (ψ w).toMonoidHom μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.2 w)) (fun τ => cochainOf B z (⇑(ψ w).toMonoidHom ∘ τ)) σ).symm

theorem tateCompactCupRes_tateCompactCohomologyResMap (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C)
    (g : A' ⟶ A) (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ}
    (h : r + s = n) (y : tateCompactCohomologyRes φ ψ A' r) (x : cohomology B s) :
    tateCompactCupRes φ ψ μ h ((tateCompactCohomologyResMap φ ψ g r).hom y) x =
      tateCompactCupRes φ ψ μ' h y ((cohomologyMap f s).hom x) := by
  rw [tateCompactCupRes_eq_homology, tateCompactCupRes_eq_homology]
  exact (LeibnizPairing.homology_homologyMap (tateCompactCupResLeibniz φ ψ μ')
    (tateCompactCupResLeibniz φ ψ μ) (tateCompactCochainsResMap φ ψ g) (cochainsMap f)
    (fun h p z => (tateCompactCupResLeibniz_naturality φ ψ μ μ' g f hμ h p z).symm) h y x).symm

end CupNatural

section DualityNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
  (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n)

theorem tateCompactDualityMap_cohomologyMap {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep (dualRep D A)] [IsDiscreteRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : tateCompactCohomologyRes φ ψ (dualRep D B) s) :
    tateCompactDualityMap φ ψ D h t B ((cohomologyMap f r).hom x) y =
      tateCompactDualityMap φ ψ D h t A x ((tateCompactCohomologyResMap φ ψ (dualMap D f) s).hom y) := by
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply,
    tateCompactCupRes_tateCompactCohomologyResMap φ ψ (dualEvalPairing D A) (dualEvalPairing D B)
      (dualMap D f) f (tensorHom_dualEvalPairing D f)]

theorem bijective_tateCompactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, IsDiscreteRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsDiscreteRep P] [IsDiscreteRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t P) := by
  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, (cohomologyMap (i j) r).hom ((cohomologyMap (p j) r).hom x) := by
    intro x
    have e := congrArg (fun φ => (cohomologyMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, cohomologyMap_id, cohomologyMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : tateCompactCohomologyRes φ ψ (dualRep D P) s,
      ∑ j, (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom
        ((tateCompactCohomologyResMap φ ψ (dualMap D (i j)) s).hom y) = y := by
    intro y
    have e := congrArg (fun F => (tateCompactCohomologyResMap φ ψ (dualMap D F) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, tateCompactCohomologyResMap_finsetSum, dualMap_id,
      tateCompactCohomologyResMap_id, tateCompactCohomologyResMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at e
    exact e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hj : ∀ j, (cohomologyMap (p j) r).hom x = 0 := by
      intro j
      apply (hX j).1
      rw [map_zero]
      ext y
      rw [AddMonoidHom.zero_apply, tateCompactDualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2
      (χ.comp (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, (cohomologyMap (i j) r).hom (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tateCompactDualityMap_cohomologyMap, ha j]
    rfl

theorem bijective_tateCompactDualityMap_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsDiscreteRep (X j)] [∀ j, Finite (X j)]
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t (⨁ X)) :=
  bijective_tateCompactDualityMap_of_sum φ ψ D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end DualityNatural

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] {N : ℕ}
  {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
  [IsDiscreteRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]

theorem tateCompactDualityMap_δ {n : ℕ} (t : tateCompactCohomologyRes φ ψ D (n + 1) →+ ZMod N)
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) {r s : ℕ}
    (h₁ : r + 1 + s = n + 1) (h₀ : r + (s + 1) = n + 1) (q : cohomology S.X₃ r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D S.X₁) s) :
    tateCompactDualityMap φ ψ D h₁ t S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      (-(-1 : ℤ) ^ s) • tateCompactDualityMap φ ψ D h₀ t S.X₃ q ((tateCompactδRes φ ψ hT s).hom y) := by
  have key := tateCompactCup_tateCompactδ_add_tateCompactCup_δ φ ψ
    (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v).toMonoidHom))
    (fun _ => 𝟙 _)
    (SAᵣ := fun w => (dualShortComplex D S).map (Rep.resFunctor (ψ w).toMonoidHom))
    (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v).toMonoidHom D) (c := fun _ => 𝟙 _)
    (Cᵣ := fun w => Rep.res (ψ w).toMonoidHom D) (cr := fun _ => 𝟙 _)
    (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X₁)
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₃))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₂))
    (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (dualEvalPairing D S.X₁))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₃))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₂))
    (fun w => (Rep.resFunctor (ψ w).toMonoidHom).map (dualEvalPairing D S.X₁))
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (fun w => resFunctor_map_comp_id (ψ w).toMonoidHom _)
    (tensorHom_dualEvalPairing D S.g) (tensorHom_dualEvalPairing D S.f).symm
    (fun v => resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun v => (resFunctor_map_naturality (φ v).toMonoidHom _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    (fun w => resFunctor_map_naturality (ψ w).toMonoidHom _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun w => (resFunctor_map_naturality (ψ w).toMonoidHom _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    hT (fun v => (Rep.shortExact_res (φ v).toMonoidHom).2 hT)
    (fun w => (Rep.shortExact_res (ψ w).toMonoidHom).2 hT) hS
    (show s + 1 + r = n + 1 by omega) (show s + (r + 1) = n + 1 by omega) y q
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply]
  exact map_eq_of_add_neg_one_pow_smul_eq_zero t s key

end Sign

end GroundTheory.ProfCoh
end
end
