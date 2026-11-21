import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigidStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaStdAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenGeometricPointsRootOfUnityEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := by
  first | exact @GlobalTheory.loc_units_eq | exact GlobalTheory.loc_units_eq | (intros; apply GlobalTheory.loc_units_eq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLift

section Algebra

open Matrix

theorem omegaStd_eq_dot {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = -(a ⬝ᵥ (Matrix.J (Fin g) ℤ *ᵥ b)) := by
  simp [omegaStd, Matrix.J, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_sub_distrib, Matrix.neg_apply]
  ring

theorem omegaStd_mulVec {g : ℕ} (T : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd (T *ᵥ a) (T *ᵥ b) = -(a ⬝ᵥ ((Tᵀ * Matrix.J (Fin g) ℤ * T) *ᵥ b)) := by
  rw [omegaStd_eq_dot, neg_inj, Matrix.mulVec_mulVec,
      ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc]

theorem exists_symplectic_hom {M g : ℕ} {G : Type} [CommGroup G] {R : Type} [CommRing R] [IsDomain R] {ζ : Rˣ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ M) (tors : ∀ x : G, x ^ M = 1)
    (card : ∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) (e : G →* G →* Rˣ) (alt : ∀ x, e x x = 1)
    (nd : ∀ x, (∀ y, e x y = 1) → x = 1) :
    ∃ l : (Fin g ⊕ Fin g → ℤ) → G, (∀ a b, l (a + b) = l a * l b) ∧ ∀ a b, e (l a) (l b) = ζ ^ omegaStd a b := by
  obtain ⟨x, hx⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing M g G R ζ hM hζ tors card e alt nd
  obtain ⟨bas, hb⟩ := exists_equiv_omegaStd (Matrix.toBilin' (Matrix.of (Out.stdSymp g))) (LinearEquiv.refl ℤ _)
    (fun i j => by simp [Matrix.toBilin'_single])
  refine ⟨fun a => ∏ i, x i ^ bas a i,
    fun a b => by simp only [map_add, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib], fun a b => ?_⟩
  rw [← hb, Matrix.toBilin'_apply]
  have s := map_prod (zpowersHom Rˣ ζ) (fun p : Fin (2 * g) × Fin (2 * g) =>
    Multiplicative.ofAdd (bas a p.1 * Out.stdSymp g p.1 p.2 * bas b p.2)) Finset.univ
  rw [← ofAdd_sum, Fintype.sum_prod_type, Fintype.prod_prod_type] at s
  refine Eq.trans ?_ s.symm
  rw [map_prod e, MonoidHom.finset_prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow, map_zpow, MonoidHom.zpow_apply, hx, ← _root_.zpow_mul, ← _root_.zpow_mul]
  simp only [zpowersHom_apply, toAdd_ofAdd]
  congr 1
  ring

theorem exists_symplectic_change {G U : Type} [CommGroup G] [CommGroup U] {h n : ℕ} {z : U}
    (hz : IsPrimitiveRoot z n) (R : G → G → U → Prop) (hR : ∀ x y c c', R x y c → R x y c' → c = c')
    (l₀ l : (Fin h ⊕ Fin h → ℤ) → G) (add₀ : ∀ a b, l₀ (a + b) = l₀ a * l₀ b) (add : ∀ a b, l (a + b) = l a * l b)
    (tors : ∀ a, l₀ a ^ n = 1) (onto : ∀ a, ∃ b, l₀ b = l a) (w₀ : ∀ a b, R (l₀ a) (l₀ b) (z ^ omegaStd a b))
    (w : ∀ a b, R (l a) (l b) (z ^ omegaStd a b)) :
    ∃ Q : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ, (∀ a b, omegaStd (Q *ᵥ a) (Q *ᵥ b) = omegaStd a b) ∧
      ∀ a, l₀ (Q *ᵥ a) = l a := by
  let F₀ : (Fin h ⊕ Fin h → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (l₀ a))
    fun a b => by rw [add₀, ofMul_mul]
  let F : (Fin h ⊕ Fin h → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (l a))
    fun a b => by rw [add, ofMul_mul]
  choose t ht using fun i => onto (Pi.single i 1)
  let T : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ := Matrix.of fun i j => t j i
  have hT : ∀ a, l₀ (T *ᵥ a) = l a := fun a => by
    have e : F₀.toIntLinearMap ∘ₗ T.mulVecLin = F.toIntLinearMap := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      show Additive.ofMul (l₀ (T *ᵥ Pi.single i 1)) = Additive.ofMul (l (Pi.single i 1))
      rw [← ht, Matrix.mulVec_single_one]
      rfl
    exact Additive.ofMul.injective (LinearMap.congr_fun e a)
  have hs : T.map (Int.castRingHom (ZMod n)) ∈ symplecticGroup (Fin h) (ZMod n) := by
    rw [SymplecticGroup.mem_iff', ← Matrix.map_J (Fin h) (Int.castRingHom (ZMod n)), ← Matrix.transpose_map,
      ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have e := w₀ (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1)
    rw [hT, hT] at e
    have e' := hR _ _ _ _ e (w _ _)
    rw [← mul_inv_eq_one, ← _root_.zpow_sub, hz.zpow_eq_one_iff_dvd, omegaStd_mulVec, omegaStd_eq_dot,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero, Int.cast_neg, Int.cast_neg, neg_inj] at e'
    simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.map_apply, eq_intCast] using e'
  obtain ⟨Q, hQ⟩ := symplecticGroupMap_zmod_surjective (Fin h) n ⟨_, hs⟩
  have hQ' : Q.1.map (Int.castRingHom (ZMod n)) = T.map (Int.castRingHom (ZMod n)) := congrArg Subtype.val hQ
  refine ⟨Q.1, fun a b => by rw [omegaStd_mulVec, SymplecticGroup.mem_iff'.1 Q.2, omegaStd_eq_dot], fun a => ?_⟩
  have d : ∀ i j, (n : ℤ) ∣ Q.1 i j - T i j := fun i j => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact congrFun (congrFun hQ' i) j
  choose D hD using d
  have e : Q.1 = T + n • Matrix.of D := by
    ext i j
    simp [← hD]
  have e' : l₀ (n • (Matrix.of D *ᵥ a)) = 1 :=
    Additive.ofMul.injective ((map_nsmul F₀ n _).trans (congrArg Additive.ofMul (tors _)))
  rw [e, Matrix.add_mulVec, Matrix.smul_mulVec, add₀, e', _root_.mul_one, hT]

end Algebra

section Geometry

open GlobalTheory.CechPic

theorem cubWeil_level {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : RigLB A}
    {c : CubicalStr A L} {k l : ℕ} {T : Over S} {x z : T ⟶ A} {ζ : Γ(T.left, ⊤)ˣ}
    (h : UU.CubWeil c (k * l) x z ζ) (hx : x ^ k = 1) : UU.CubWeil c k x (z ^ l) ζ := by
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨ζ', h', -⟩ := UU.existsUnique_cubWeil c (N := k) (x := x) (y := z ^ l) hx
    (by rw [← pow_mul, mul_comm, h.2.1])
  have a := (UU.cubWeil_iff_weilIs hG hA h.2.1 h.1 _).1 h.symm
  have b := (UU.cubWeil_iff_weilIs hG hA h'.2.1 h'.1 _).1 h'.symm
  rw [Nat.cast_mul] at a
  rwa [inv_injective (PairingLevels.weilIs_value_eq hG hA L.isLB c.isGen a b)]

variable {K o : Type} [Field K] [CommRing o] {s : Sp K ⟶ Sp o} {h n : ℕ} {ζ : o}

theorem pull_mul_left (c : SiegPre h n ζ s) (hc : c.Principal) {T : Over (Sp K)} (x x' y : T ⟶ c.A) :
    pull (lift (x * x') y).left (cls c.P c.isLB) =
      pull (lift x y).left (cls c.P c.isLB) + pull (lift x' y).left (cls c.P c.isLB) := by
  have hL := c.isLB
  have hΘ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow K c.A c.diag c.P c.ab
    (pull_isLB hL _) hc.1 hL).1
  have ax₁ : ∀ u : T ⟶ c.A, pull (lift (1 : T ⟶ c.A) u).left (cls c.P hL) = 0 := fun u => by
    have e := (cls_eq_zero_iff (pull_isLB hL _)).2 c.rig₁
    rw [cls_pull hL] at e
    have e' := congrArg (pull u.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  have ax₂ : ∀ u : T ⟶ c.A, pull (lift u (1 : T ⟶ c.A)).left (cls c.P hL) = 0 := fun u => by
    have e := (cls_eq_zero_iff (pull_isLB hL _)).2 c.rig₂
    rw [cls_pull hL] at e
    have e' := congrArg (pull u.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  have lm : ∀ a b a' b' : T ⟶ c.A, lift a b * lift a' b' = lift (a * a') (b * b') := fun a b a' b' => by
    ext1 <;> simp [MonObj.mul_comp]
  have l1 : (1 : T ⟶ c.A ⊗ c.A) = lift 1 1 := by ext1 <;> simp [MonObj.one_comp]
  have lamv : ∀ a b : T ⟶ c.A, lam (cls _ hL) (lift a 1) (lift 1 b) = pull (lift a b).left (cls c.P hL) := fun a b => by
    rw [lam, lm, l1, ax₁, ax₁, ax₂, _root_.mul_one, _root_.one_mul, sub_zero, sub_zero, add_zero]
  have key := lam_mul_left hL hΘ (lift x 1) (lift x' 1) (lift 1 y)
  rwa [lm, _root_.mul_one, lamv, lamv, lamv] at key

theorem sq_eq_one_of_translDiff (c : SiegPre h n ζ s) (hc : c.Principal) {F : Type} [Field F] (t : Sp F ⟶ Sp K)
    (x : Over.mk t ⟶ c.A) (hx : AbLaw.Triv (Out.translDiff c.A c.diag x)) : x ^ 2 = 1 := by
  have hL := c.isLB
  have hD : c.diag.IsLB := pull_isLB hL _
  have sy : ∀ {T : Over (Sp K)} (a b : T ⟶ c.A),
      pull (lift a b).left (cls c.P hL) = pull (lift b a).left (cls c.P hL) := fun a b => by
    have e := (cls_eq_iff hL (pull_isLB hL _)).2 c.symm
    rw [cls_pull hL] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]
  have dg : ∀ {T : Over (Sp K)} (a : T ⟶ c.A), pull a.left (cls _ hD) = pull (lift a a).left (cls c.P hL) := fun a => by
    refine (congrArg (pull a.left) (cls_pull hL _ hD)).trans ?_
    rw [← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have x0 : pull (lift x x).left (cls c.P hL) = 0 :=
    (cls_pull hL _ (pull_isLB hL _)).symm.trans ((cls_eq_zero_iff (pull_isLB hL _)).2
      (DVR.exists_gen_of_isLB_local (V := F) _ (pull_isLB hL _)))
  have e := (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).2 hx
  rw [cls_linComb hD, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [← Hom.mul_def] at e
  have e' := congrArg (pull (lift (snd c.A (Over.mk t)) (fst c.A (Over.mk t))).left) e
  rw [map_zero, map_add, map_neg, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_fst_assoc, lift_snd, dg, dg, pull_mul_left c hc, sy _ (_ * _), sy _ (_ * _), pull_mul_left c hc,
    pull_mul_left c hc, ← comp_lift, Over.comp_left, pull_comp, x0, map_zero] at e'
  refine hc.2 _ _ ((cls_eq_zero_iff (pull_isLB hL _)).1 ?_)
  rw [cls_pull hL, pow_two, MonObj.comp_mul, pull_mul_left c hc, ← e', sy (fst c.A (Over.mk t)) (_ ≫ x)]
  abel

end Geometry

theorem exists_lift {h n d : ℕ} {k : Type} [Field k] [IsAlgClosed k] (b : TBase k (n * d)) {ζ' : k}
    (hζ' : ζ' = (b.ζ : k) ^ d) (c : SiegPre h n ζ' (𝟙 (Sp k))) (hn : 3 ≤ n) (ho : Odd (n * d)) (hc : c.Principal) :
    ∃ C : SiegPre h (n * d) (b.ζ : k) (𝟙 (Sp k)), SRel C c d 1 (𝟙 _) := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((n * d : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : n * d ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hn₀ : n ≠ 0 := by omega
  have hd₀ : d ≠ 0 := right_ne_zero_of_mul hN₀
  have hz : IsPrimitiveRoot b.ζ (n * d) := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) (n * d) := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have hz₃ : IsPrimitiveRoot ((b.ζ ^ 2) ^ d) n := hz₂.pow (Nat.pos_of_ne_zero hN₀) (mul_comm n d)
  have hu : ∀ y : 𝟙_ (Over (Sp k)) ⟶ c.A, toUnit (Over.mk (𝟙 (Sp k))) ≫ y = y := fun y =>
    (congrArg (· ≫ y) (toUnit_unique _ (𝟙 (𝟙_ (Over (Sp k)))))).trans (Category.id_comp _)
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k (𝟙 _) (RingHom.id k) (b.ζ ^ d)
    ((Category.id_comp _).trans (Spec.map_id _).symm) (by rw [hζ']; rfl)
  simp only [hu] at g₁ g₂ g₃

  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k c.A c.ab
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg
  obtain rfl : h = g := by
    have hnk : (n : k) ≠ 0 := left_ne_zero_of_mul (by rwa [Nat.cast_mul] at hN)
    have : NeZero n := ⟨hn₀⟩
    let F : (Fin h ⊕ Fin h → ZMod n) → {y : Over.mk (𝟙 (Sp k)) ⟶ c.A // y ^ n = 1} :=
      fun a => ⟨c.lev fun i => (a i).val, c.lev_tors _⟩
    have hF : Function.Bijective F := by
      refine ⟨fun a a' e => ?_, fun y => ?_⟩
      · have e₁ : c.lev (fun i => (a i).val) = c.lev fun i => (a' i).val := congrArg Subtype.val e
        have e₂ := c.lev_add ((fun i => ((a i).val : ℤ)) - fun i => ((a' i).val : ℤ)) fun i => (a' i).val
        rw [sub_add_cancel, e₁] at e₂
        obtain ⟨v, hv⟩ := (g₁ _).1 (mul_eq_right.1 e₂.symm)
        funext i
        have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hv i)
        simpa [sub_eq_zero] using this
      · obtain ⟨a, ha⟩ := g₂ y.1 y.2
        refine ⟨fun i => a i, Subtype.ext (Eq.trans ?_ ha)⟩
        have e₂ := c.lev_add (fun i => (((a i : ZMod n)).val : ℤ)) (n • fun i => a i / n)
        have e₃ : c.lev (n • fun i => a i / n) = 1 := (g₁ _).2 ⟨_, rfl⟩
        rw [e₃, _root_.mul_one] at e₂
        refine e₂.symm.trans (congrArg c.lev (funext fun i => ?_))
        simp only [ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
        exact Int.emod_add_mul_ediv _ _
    have e := (Nat.card_congr (Equiv.ofBijective F hF)).trans (card k (𝟙 _) n hnk)
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_fin] at e
    have := Nat.pow_right_injective (by omega : 2 ≤ n) e
    omega

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 (n * d) (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom (n * d)).ker
  have hH : ∀ x : H, x.1 ^ (n * d) = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu (n * d) x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu (n * d) x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := h) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ (n * d) = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) (n * d) hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ (n * d) = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu (n * d) (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A), (∀ a a', lev (a + a') = lev a * lev a') →
      (∀ a a', UU.CubWeil cu (n * d) (lev a) (lev a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a'))) →
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ v, a = (n * d) • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ (n * d) = 1 → ∃ a, toUnit _ ≫ lev a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (n * d : ℕ) (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro lev add weil k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have tors : ∀ a, lev a ^ (n * d) = 1 := fun a => (weil a a).1
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) (n * d) :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((n * d : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu (n * d) (toUnit (Over.mk (spMap β)) ≫ lev a) (toUnit _ ≫ lev a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (weil a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ lev a = 1 → ∃ v, a = (n * d) • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, lev (m • v) = lev v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
      rw [pw, tors, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  obtain ⟨k₁, k₂, -⟩ := mk l₂ add₂ w₂ k (𝟙 _) (RingHom.id k) b.ζ
    ((Category.id_comp _).trans (Spec.map_id _).symm) rfl
  simp only [hu] at k₁ k₂
  have pw : ∀ (m : ℕ) v, l₂ (m • v) = l₂ v ^ m := fun m v => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
    | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
  have tors₃ : ∀ a, (l₂ a ^ d) ^ n = 1 := fun a => by rw [← pow_mul, mul_comm, tors₂]
  obtain ⟨Q, hQ, hQl⟩ := exists_symplectic_change hz₃ (fun x y u => Out.WeilIs c.A c.diag n x y (unitOn u))
    (fun x y u u' H H' => SiegelOfPolarised.unitOn_inj (CommutatorPairing.weilIs_unique hG c.ab hD H H'))
    (fun a => l₂ a ^ d) c.lev (fun a a' => by rw [add₂, mul_pow]) c.lev_add tors₃
    (fun a => by
      obtain ⟨v, hv⟩ := k₂ (c.lev a) (show c.lev a ^ (n * d) = 1 by rw [pow_mul, c.lev_tors, one_pow])
      have hv' : l₂ v = c.lev a := hv
      obtain ⟨v', hv''⟩ := (k₁ (n • v)).1 (show l₂ (n • v) = 1 by rw [pw, hv', c.lev_tors])
      rw [mul_smul] at hv''
      refine ⟨v', ?_⟩
      rw [← pw, ← smul_right_injective _ hn₀ hv'', hv'])
    (fun a a' => by
      have H := toW (cubWeil_level c.ab ((w₂ a a').pow_left d) (tors₃ a))
      unfold unitOn at H ⊢
      rwa [← map_pow, ← zpow_natCast (_ ^ omegaStd a a'), ← zpow_mul, mul_comm (omegaStd a a'), zpow_mul,
        zpow_natCast] at H)
    (fun a a' => by
      have H := g₃ a a'
      rwa [zpow_mul, zpow_ofNat, pow_right_comm] at H)
  have add₄ : ∀ a a', l₂ (Q.mulVec (a + a')) = l₂ (Q.mulVec a) * l₂ (Q.mulVec a') := fun a a' => by
    rw [Matrix.mulVec_add, add₂]
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := fun a => l₂ (Q.mulVec a)
            lev_add := add₄
            lev_tors := fun a => tors₂ _
            geom := mk _ add₄ fun a a' => hQ a a' ▸ w₂ _ _ },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · show (l₂ (Q.mulVec a) ^ d).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.lev a ^ 1).left
    rw [hQl, pow_one, Category.comp_id, Category.id_comp]

theorem exists_level_lift : ∀ (h n N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (b : TBase k N) (c : SiegPre h n ((b.ζ : k) ^ (N / n)) (𝟙 (Sp k))), 3 ≤ n → Odd N → n ∣ N → c.Principal → ∃ C : SiegPre h N (b.ζ : k) (𝟙 (Sp k)), SRel C c (N / n) 1 (𝟙 _) := by
  rintro h n N k _ _ b c hn ho ⟨d, rfl⟩ hc
  have e : n * d / n = d := Nat.mul_div_cancel_left d (by omega)
  obtain ⟨C, hC⟩ := exists_lift b (congrArg ((b.ζ : k) ^ ·) e) c hn ho hc
  refine ⟨C, ?_⟩
  convert hC using 1

end GlobalTheory.SiegLift
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegGeomLift

def baseAt {B : Type} [CommRing B] {N : ℕ} (b : TBase B N) {k : Type} [Field k] (β : B →+* k) : TBase k N where
  ζ := Units.map β.toMonoidHom b.ζ
  unit := by simpa using b.unit.map β
  prim := fun K _ β' => b.prim K (β'.comp β)

theorem exists_geom_level : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  intro h n N B _ b ζ₀ S s c k _ _ x β hn ho hd hζ hc hx
  let bk := baseAt b β
  have hj : β ζ₀ = (bk.ζ : k) ^ (N / n) := by rw [hζ, map_pow]; rfl
  obtain ⟨P₁, P₂, -⟩ := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B k ζ₀ _ β S (Sp k) s (𝟙 (Sp k)) x hj
    (by rw [hx, Category.id_comp])
  obtain ⟨c', hpb⟩ := P₁ c
  have hc' := P₂ c c' hpb hc
  obtain ⟨C, φC, pbC, ⟨φ₂C, sqC, isoC⟩, lowC⟩ := GlobalTheory.SiegLift.exists_level_lift h n N k bk c' hn ho hd hc'
  obtain ⟨φx, φ₂x, pbx, sqx, isox, levx⟩ := hpb
  let T0 : Over (Sp k) := 𝟙_ (Over (Sp k))
  have pb := IsGrpPullback.comp pbC pbx
  have wU : 𝟙 (Sp k) ≫ (T0.hom ≫ 𝟙 (Sp k) ≫ x) = x := by simp [T0]
  let U : Over.mk x ⟶ Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) := Over.homMk (𝟙 (Sp k)) wU
  let V : Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 (Sp k)) (by simp [T0])
  have VU : V ≫ U = 𝟙 _ := by ext; simp [U, V]; try rfl
  have UV : U ≫ V = 𝟙 _ := by ext; simp [U, V]; try rfl
  let ψ : (T0 ⟶ C.A) →* (Over.mk x ⟶ c.A) := (preHom U).comp (pushHom pb T0)
  have ψl : ∀ g : T0 ⟶ C.A, (ψ g).left = g.left ≫ φC ≫ φx := fun g => by
    show 𝟙 (Sp k) ≫ g.left ≫ φC ≫ φx = _
    simp
  have ψi : Function.Injective ψ := fun g g' e => by
    refine GlobalTheory.SiegelPull.push_injective pb T0 ?_
    have e' := congrArg (V ≫ ·) e
    simpa [ψ, preHom, ← Category.assoc, VU] using e'
  have ψs : Function.Surjective ψ := fun g => by
    obtain ⟨y, hy⟩ := GlobalTheory.SiegelPull.push_surjective pb T0 (V ≫ g)
    refine ⟨y, ?_⟩
    show U ≫ pushHom pb T0 y = g
    rw [hy, ← Category.assoc, UV, Category.id_comp]
  have hu : ∀ y : T0 ⟶ C.A, toUnit (Over.mk (𝟙 (Sp k))) ≫ y = y := fun y =>
    (congrArg (· ≫ y) (toUnit_unique _ (𝟙 T0))).trans (Category.id_comp _)
  obtain ⟨g₁, g₂, g₃⟩ := C.geom k (𝟙 _) (RingHom.id k) bk.ζ
    ((Category.id_comp _).trans (Spec.map_id _).symm) rfl
  simp only [hu] at g₁ g₂ g₃
  refine ⟨fun a => ψ (C.lev a), fun a a' => show ψ (C.lev (a + a')) = ψ (C.lev a) * ψ (C.lev a') by rw [C.lev_add, map_mul], fun a => show ψ (C.lev a) ^ N = 1 by rw [← map_pow, C.lev_tors, map_one],
    fun a => ?_, fun a => ?_, fun g hg => ?_, fun a a' => ?_⟩
  · apply Over.OverMorphism.ext
    rw [← map_pow, ψl, ← Category.assoc, lowC, pow_one, Category.id_comp, levx, Over.comp_left, Over.toUnit_left]
    rfl
  · rw [← map_one ψ, ψi.eq_iff]
    exact g₁ a
  · obtain ⟨y, rfl⟩ := ψs g
    obtain ⟨a, ha⟩ := g₂ y (ψi (by rw [map_pow, hg, map_one]))
    exact ⟨a, show ψ (C.lev a) = ψ y by rw [ha]⟩
  · have W1 := (GlobalTheory.weilIs_grpPullback_of_comm (Sp k) (Sp k) c'.A C.A (𝟙 (Sp k)) φC _ _ (pull_isLB c'.isLB _)
      (pull_isLB C.isLB _) pbC (GlobalTheory.SiegelPull.diag_iso sqC isoC) T0 N (C.lev a) (C.lev a')
      (pushHom pbC T0 (C.lev a)) (pushHom pbC T0 (C.lev a')) _ rfl rfl).1 (g₃ a a')
    have W2 := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp k) c.A c'.A x φx _ _ (pull_isLB c.isLB _)
      (pull_isLB c'.isLB _) pbx (GlobalTheory.SiegelPull.diag_iso sqx isox) (Over.mk (T0.hom ≫ 𝟙 (Sp k))) N _ _
      (pushHom pbx _ (pushHom pbC T0 (C.lev a))) (pushHom pbx _ (pushHom pbC T0 (C.lev a'))) _ rfl rfl).1 W1
    exact GlobalTheory.SiegCover.weilIs_congr_base (by simp [T0]) ((Category.assoc _ _ _).trans (ψl _).symm)
      ((Category.assoc _ _ _).trans (ψl _).symm) W2

end GlobalTheory.SiegGeomLift
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  atlas_forward_decl GlobalTheory.SiegGeomLift.exists_geom_level
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomBasis

theorem basis_of_weil : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  intro h N k _ S x A _ _ L z e₀ e hL hN hz add₀ ker₀ onto₀ add tors weil
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hN) (by decide)
  haveI : NeZero N := ⟨hN0⟩
  have e0 : e 0 = 1 := GlobalTheory.LevCover.add_map_zero add
  have kerE : ∀ a, e a = 1 ↔ ∃ a', a = N • a' := by
    intro a
    constructor
    · intro ha
      apply GlobalTheory.SiegelOfPolarised.exists_smul_of_dvd
      intro b
      have w1 := weil a b
      have w0 := weil 0 b
      rw [ha] at w1
      rw [e0] at w0
      have hu := GlobalTheory.weilIs_unique_fieldPoint S A L hL k x _ _ _ _ _ w1 w0
      have h0 : omegaStd (0 : Fin h ⊕ Fin h → ℤ) b = 0 := by simp [omegaStd]
      rw [h0, mul_zero, zpow_zero] at hu
      have hd : (N : ℤ) ∣ 2 * omegaStd a b := (hz.zpow_eq_one_iff_dvd _).1 hu
      obtain ⟨m, hm⟩ := hN
      have hc : IsCoprime (N : ℤ) 2 := ⟨1, -(m : ℤ), by rw [hm]; push_cast; ring⟩
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨b, rfl⟩
      rw [GlobalTheory.LevCover.add_map_nsmul add, tors]
  have tors₀ : ∀ a, e₀ a ^ N = 1 := fun a => by
    rw [← GlobalTheory.LevCover.add_map_nsmul add₀]; exact (ker₀ _).2 ⟨a, rfl⟩
  let F : (Fin h ⊕ Fin h → ZMod N) → {g : Over.mk x ⟶ A // g ^ N = 1} :=
    fun c => ⟨e₀ fun i => ((c i).val : ℤ), tors₀ _⟩
  have hF : Function.Injective F := fun c c' hcc => by
    have e₁ : e₀ (fun i => ((c i).val : ℤ)) = e₀ fun i => ((c' i).val : ℤ) := congrArg Subtype.val hcc
    have e₂ := add₀ ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => ((c' i).val : ℤ)
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker₀ _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun w : ℤ => (w : ZMod N)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hF' : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := onto₀ g hg
    refine ⟨fun i => (a i : ZMod N), Subtype.ext ?_⟩
    show e₀ (fun i => (((a i : ZMod N)).val : ℤ)) = e₀ a
    have d : ∀ i, (N : ℤ) ∣ a i - (((a i : ZMod N)).val : ℤ) := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp)
    choose b hb using d
    have hab : a - (fun i => (((a i : ZMod N)).val : ℤ)) = N • b := funext fun i => by simpa using hb i
    have := add₀ (a - fun i => (((a i : ZMod N)).val : ℤ)) fun i => (((a i : ZMod N)).val : ℤ)
    rw [sub_add_cancel, hab, (ker₀ _).2 ⟨b, rfl⟩, _root_.one_mul] at this
    exact this.symm
  have card : Nat.card {g : Over.mk x ⟶ A // g ^ N = 1} = N ^ Fintype.card (Fin h ⊕ Fin h) := by
    rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hF'⟩), Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  exact ⟨kerE, GlobalTheory.SiegelOfPolarised.onto_torsion hN0 e add tors (fun a ha => (kerE a).1 ha) card⟩

end GlobalTheory.GeomBasis
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_torsion_of_weilPairing_field : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  atlas_forward_decl GlobalTheory.GeomBasis.basis_of_weil
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp GlobalTheory.SiegLevCalc

section Sec

variable {S V : Scheme.{0}} {A : Over S} {A' : Over V} [GrpObj A] [GrpObj A'] {π : V ⟶ S} {φ : A'.left ⟶ A.left}

def secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : 𝟙_ (Over V) ⟶ A' :=
  Over.homMk (hp.1.lift x.left (𝟙 V) ((Over.w x).trans (Category.id_comp π).symm)) (hp.1.lift_snd _ _ _)

theorem secOf_left (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : (secOf hp x).left ≫ φ = x.left :=
  hp.1.lift_fst _ _ _

theorem push_secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (T : Over V) :
    pushHom hp T (toUnit T ≫ secOf hp x) = (Over.homMk T.hom rfl : Over.mk (T.hom ≫ π) ⟶ Over.mk π) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secOf hp x).left) ≫ φ = T.hom ≫ x.left
  rw [Category.assoc, secOf_left, Over.toUnit_left]

theorem push_secOf' (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) :
    pushHom hp _ (secOf hp x) =
      (Over.homMk (𝟙_ (Over V)).hom rfl : Over.mk ((𝟙_ (Over V)).hom ≫ π) ⟶ Over.mk π) ≫ x := by
  have e := push_secOf hp x (𝟙_ (Over V))
  rwa [toUnit_unit, Category.id_comp] at e

theorem secOf_mul (hp : IsGrpPullback A' A π φ) (x y : Over.mk π ⟶ A) :
    secOf hp (x * y) = secOf hp x * secOf hp y :=
  push_injective hp _ (by rw [map_mul, push_secOf', push_secOf', push_secOf', MonObj.comp_mul])

theorem secOf_pow (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (k : ℕ) :
    secOf hp (x ^ k) = secOf hp x ^ k :=
  push_injective hp _ (by rw [map_pow, push_secOf', push_secOf', MonObj.comp_pow])

theorem secOf_one (hp : IsGrpPullback A' A π φ) : secOf hp (1 : Over.mk π ⟶ A) = 1 :=
  push_injective hp _ (by rw [map_one, push_secOf', MonObj.comp_one])

end Sec

section Rel

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem comp_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {ψ : c''.A.left ⟶ c'.A.left}
    {ψ₂ : (G2 c''.A).left ⟶ (G2 c'.A).left} (hψ : IsGrpPullback c''.A c'.A f' ψ) (hs' : IsSquare ψ ψ₂)
    (hw' : LBIso c''.P (c'.P.pull ψ₂)) :
    IsGrpPullback c''.A c.A (f' ≫ f) (ψ ≫ φ) ∧
      ∃ χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left, IsSquare (ψ ≫ φ) χ₂ ∧ LBIso c''.P (c.P.pull χ₂) := by
  refine ⟨hψ.comp hφ, ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem cancel_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {χ : c''.A.left ⟶ c.A.left}
    {χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left} (hχ : IsGrpPullback c''.A c.A (f' ≫ f) χ) (hs' : IsSquare χ χ₂)
    (hw' : LBIso c''.P (c.P.pull χ₂)) (hl : ∀ a, (c''.lev a).left ≫ χ = f' ≫ (c'.lev a).left ≫ φ) :
    SiegPB c'' c' f' := by
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, hl a, Category.assoc]
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

end Rel

section Cover

variable {h n N : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {S V : Scheme.{0}} {s : S ⟶ Sp B}

def pair (c : SiegPre h n ζ s) (π : V ⟶ S) : ReciprocityTheory.ChartRestriction.G.Pdiv.SiegPairPB c π :=
  Classical.choice (siegPairPB_nonempty c π)

def cover (c : SiegPre h n ζ s) (sV : V ⟶ Sp B') (ζ' : B') (π : V ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A))
    (hadd : ∀ a a', e (a + a') = e a * e a') (htor : ∀ a, e a ^ N = 1)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) :
    SiegPre h N ζ' sV where
  A := (pair c π).A
  ab := (pair c π).ab
  P := (pair c π).P
  isLB := (pair c π).isLB
  rig₁ := (pair c π).rig₁
  rig₂ := (pair c π).rig₂
  symm := (pair c π).symm
  lev a := secOf (pair c π).pb (e a)
  lev_add a b := by rw [hadd, secOf_mul]
  lev_tors a := by rw [← secOf_pow, htor, secOf_one]
  geom k _ _ x β z hx hz := by
    obtain ⟨g₁, g₂, g₃⟩ := hgeom k x β z hx hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective (pair c π).pb (Over.mk x)).eq_iff, push_secOf, map_one]
      try rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom (pair c π).pb (Over.mk x) g) (by
        have := congrArg (pushHom (pair c π).pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective (pair c π).pb _ ((push_secOf _ _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S V c.A (pair c π).A π (pair c π).φ _ _ (pull_isLB c.isLB _)
        (pull_isLB (pair c π).isLB _) (pair c π).pb (diag_iso (pair c π).sq (pair c π).iso) (Over.mk x) N _ _ _ _ _
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e b) (Over.mk x)).symm)).2 (g₃ a b)

end Cover

end GlobalTheory.SiegCover

namespace GlobalTheory

open SiegCover SiegLevCalc

theorem siegCover_build : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := by
  intro h n N d B B' _ _ ζ ζ' S V s sV π c e hadd htor hd hgeom
  have levd : ∀ a, ((cover c sV ζ' π e hadd htor hgeom).lev a ^ d).left ≫ (pair c π).φ = π ≫ (c.lev a ^ 1).left := by
    intro a
    show (secOf (pair c π).pb (e a) ^ d).left ≫ _ = _
    rw [← secOf_pow, secOf_left, hd a, pow_one, Over.comp_left, Over.toUnit_left]
    try rfl
  refine ⟨cover c sV ζ' π e hadd htor hgeom, (pair c π).φ,
    ⟨(pair c π).pb, ⟨(pair c π).φ₂, (pair c π).sq, (pair c π).iso⟩, levd⟩, fun a => secOf_left (pair c π).pb (e a), ?_⟩
  intro T t B'' _ ζ'' sT C'
  constructor
  · rintro ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩
    obtain ⟨hc, χ₂, hsq, hiso⟩ := comp_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq
      (pair c π).iso hψ hs' hw'
    refine ⟨ψ ≫ (pair c π).φ, ⟨hc, ⟨χ₂, hsq, hiso⟩, fun a => ?_⟩, fun a => ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (pow_section hψ _ _ (hl' a) d)).trans
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (levd a)).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (hl' a)).trans
        ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a)))))
  · rintro ⟨φ', ⟨hχ, ⟨χ₂, hs', hw'⟩, -⟩, hl'⟩
    exact cancel_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq (pair c π).iso hχ hs' hw'
      fun a => (hl' a).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a))).symm

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_deeper_level_of_sections : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := by
  atlas_forward_decl GlobalTheory.siegCover_build
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem locEq : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit

theorem pairValue : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N → IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 → ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := GlobalTheory.DiagPairing.exists_weilIs_diag_root

theorem geomLift : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel

theorem geomBij : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := GlobalTheory.T.basis_torsion_of_weilPairing_field

theorem buildCover : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := GlobalTheory.T.exists_siegelObject_deeper_level_of_sections

open GlobalTheory.LevCover in

theorem exists_levelCover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  intro h n N B B' _ _ ζ b j S s' c hn hN hnN hζ hc
  have hNpos : 0 < N := hN.pos
  have hnodd : Odd n := hN.of_dvd_nat hnN
  have hNn : N / n * n = N := Nat.div_mul_cancel hnN
  let b₀ : TBase B' n :=
    { ζ := b.ζ ^ (N / n)
      unit := by
        have := b.unit
        rw [← hNn, Nat.cast_mul] at this
        exact isUnit_of_mul_isUnit_right this
      prim := fun K _ β => by
        rw [Units.val_pow_eq_pow_val, map_pow]
        exact (b.prim K β).pow hNpos hNn.symm }
  have hb₀ : (b₀.ζ : B') = (b.ζ : B') ^ (N / n) := Units.val_pow_eq_pow_val _ _
  have hj : j ζ = (b₀.ζ : B') := hζ.trans hb₀.symm
  have RC := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B B' ζ (b₀.ζ : B') j S S (s' ≫ spMap j) s' (𝟙 S) hj
    (Category.id_comp _)
  obtain ⟨c₀, hpb⟩ := RC.1 c
  have hc₀ : c₀.Principal := RC.2.1 c c₀ hpb hc
  have hrel : ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')),
      SRel C' c₀ (N / n) 1 t ↔ SRel C' c (N / n) 1 t := fun T t C' => by
    have := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n N B B' B' ζ (b₀.ζ : B') (b.ζ : B') S S T (s' ≫ spMap j) s' (t ≫ s') c c₀ C'
      (𝟙 S) t 1 1 (N / n) ((sRel_one_one_iff c₀ c (𝟙 S)).2 hpb)).1
    rwa [Category.comp_id] at this
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (fnOn s')
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, hadd, hpow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S c₀.A N (Fin h ⊕ Fin h → ℤ) c₀.ab hNS
  have R : RepTors c₀.A N _ Z et := ⟨hfin, het, hadd, hpow, huniv⟩
  haveI := hfin
  haveI := het
  have hNZ : IsUnit (N : Γ(Z.left, ⊤)) := by
    have := hNS.map Z.hom.appTop.hom
    rwa [map_natCast] at this
  have hlevN : ∀ a, c₀.lev a ^ N = 1 := fun a => by
    rw [← hNn, mul_comm, pow_mul, c₀.lev_tors, one_pow]
  obtain ⟨Ul, hUl, HUl⟩ := R.clopenCond (fun a => et a ^ (N / n)) (fun a => toUnit Z ≫ c₀.lev a)
    (fun a a' => by rw [hadd, mul_pow]) (fun a => by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow])
    (fun a a' => by rw [c₀.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hlevN, MonObj.comp_one])
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : c₀.diag.IsLB := pull_isLB c₀.isLB _
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a a' k _ _ g =>
    ∀ β : B' →+* k, g ≫ Z.hom ≫ s' = spMap β →
      Out.WeilIs c₀.A c₀.diag N ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a)
        ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a')
        (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a')))
  have hzN : ∀ (k : Type) [Field k] (β : B' →+* k), Units.map β.toMonoidHom b.ζ ^ N = 1 := fun k _ β =>
    Units.ext (by simpa using (b.prim k β).pow_eq_one)
  have locPair : ∀ a a', HkClopen.Loc (P2 a a') := fun a a' => by
    obtain ⟨v, hv, hW⟩ := pairValue h n B' _ S s' c₀ N Z (et a) (et a') hc₀.1 hNpos hNZ (hpow a) (hpow a')
    refine (locEq Z.left N v (Units.map (fnOn (Z.hom ≫ s')).toMonoidHom (b.ζ ^ (2 * omegaStd a a'))) hNZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      rw [map_fnOn _ g β hβ, ← unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hzN, one_zpow]
      exact unitOn_one'
    · have hW' := CommPairing.weilIs_pull hG c₀.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      have hu := map_fnOn _ g β hβ (b.ζ ^ (2 * omegaStd a a'))
      rw [show Units.map β.toMonoidHom (b.ζ ^ (2 * omegaStd a a')) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') from map_zpow _ _ _] at hu
      constructor
      · intro e β' hβ'
        obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans hβ)
        rw [← hu, ← e]
        exact hW'
      · intro H
        exact CommutatorPairing.weilIs_unique hG c₀.ab hLB hW' (hu ▸ H β hβ)

  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hNpos
  haveI := hκ
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + N • c₁) (a' + N • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β hβ
    have e1 : ∀ a c, et (a + N • c) = et a := fun a c => by rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
    rw [e1, e1]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + N • c₁) (a' + N • c₂) = omegaStd a a' + N * m :=
      ⟨_, omegaStd_add_nsmul N a a' c₁ c₂⟩
    have hz : Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd (a + N • c₁) (a' + N • c₂)) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (N * m) = N * (2 * m) by ring, zpow_mul _ (N : ℤ), zpow_natCast,
        hzN, one_zpow, _root_.mul_one]
    rw [hz]
    exact H β hβ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨Wp, hWp, HWp⟩ := localization₂
  let U : Z.left.Opens := Ul ⊓ ⟨Wp, hWp.isOpen⟩
  have hU : IsClosed (U : Set Z.left) := hUl.inter hWp.isClosed
  obtain ⟨V, i, hV1, hV2, hi, Hi⟩ := exists_sub U hU
  have memWp : ∀ (Tw : Over S) (w : Tw ⟶ Z), (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Tw.left) (a a'),
      P2 a a' k (x ≫ w.left)) → Set.range w.left ⊆ Wp := by
    rintro Tw w H _ ⟨p, rfl⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point Tw.left p
    have h₁ := (HWp k (x ≫ w.left)).2 (H k x)
    have hp : x (default : PrimeSpectrum k) = p := by
      have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at this
    exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left p by rw [← hp]; rfl) ▸ h₁
  have hir : Set.range i.left ⊆ U := (Hi V i).2 ⟨𝟙 _, Category.id_comp _⟩
  have hiL := (HUl V i).2 fun _ hp => (hir hp).1
  have iW : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V.left) (a a'), P2 a a' k (x ≫ i.left) :=
    fun k _ _ x => (HWp k (x ≫ i.left)).1 (hir ⟨x (default : PrimeSpectrum k), rfl⟩).2

  have hprim : ∀ (k : Type) [Field k] (β : B' →+* k), IsPrimitiveRoot (Units.map β.toMonoidHom b.ζ) N :=
    fun k _ β => IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
  obtain ⟨C, φ, hsrel, hlev, huniv'⟩ := buildCover h n N (N / n) B' B' (b₀.ζ : B') (b.ζ : B') S V.left s'
    (V.hom ≫ s') V.hom c₀ (fun a => i ≫ et a) (fun a a' => by rw [hadd, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one])
    (fun a => by rw [← MonObj.comp_pow, hiL a, comp_toUnit_assoc]; rfl)
    (fun k _ _ x β z hx hz => by
      obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hz
      have hxS : (x ≫ V.hom) ≫ s' = spMap β := by rw [Category.assoc]; exact hx
      obtain ⟨e₀, a1, -, -, k1, o1, -⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k (x ≫ V.hom) β hn hN hnN hb₀
        hc₀ hxS
      have hpair : ∀ a a', Out.WeilIs c₀.A c₀.diag N
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a)
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a')
          (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := fun a a' =>
        weilIs_congr_base (by rw [Category.assoc, Over.w i]) (by simp) (by simp)
          (iW k x a a' β (by rw [← hx, Category.assoc, reassoc_of% (Over.w i)]))
      obtain ⟨b1, b2⟩ := geomBij h N k S (x ≫ V.hom) c₀.A c₀.diag (Units.map β.toMonoidHom b.ζ) e₀
        (fun a => (Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a) hLB hN (hprim k β) a1 k1 o1
        (fun a a' => by simp only [hadd, MonObj.comp_mul])
        (fun a => by rw [← MonObj.comp_pow, ← MonObj.comp_pow, hpow, MonObj.comp_one, MonObj.comp_one]) hpair
      exact ⟨b1, b2, hpair⟩)

  have h1T : ∀ (T : Scheme.{0}), (𝟙_ (Over T)).hom = 𝟙 T := fun T => rfl
  refine ⟨V.left, V.hom, C, hV1, hV2, ⟨fun pt => ?_⟩, (hrel V.left V.hom C).1 ⟨φ, hsrel⟩, fun T t C' hC' => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s')
    obtain ⟨e₀, a1, p1, l1, -, -, w1⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k x β hn hN hnN hb₀ hc₀ hβ
    obtain ⟨w, hw, -⟩ := huniv (Over.mk x) e₀ a1 p1
    have hx' : w.left ≫ Z.hom = x := Over.w w
    have hwl : Set.range w.left ⊆ Ul := (HUl (Over.mk x) w).1 fun a => by
      rw [MonObj.comp_pow, hw, l1, comp_toUnit_assoc]
    have hwW : w.left (default : PrimeSpectrum k) ∈ Wp := (HWp k w.left).2 fun a a' β' hβ' => by
      obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans (by rw [← Category.assoc, hx', hβ]))
      exact weilIs_congr_base hx'.symm (by rw [← hw a]; rfl) (by rw [← hw a']; rfl) (w1 a a')
    obtain ⟨w', hw'⟩ := (Hi _ w).1 fun _ hq => ⟨hwl hq, (HkClopen.range_subset_iff w.left Wp).2 hwW hq⟩
    obtain ⟨p, hp⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨w'.left p, by rw [← Scheme.Hom.comp_apply, Over.w w']; exact hp⟩
  · obtain ⟨φ', pb', hφ', low'⟩ := (hrel T t C').2 hC'
    let Tt : Over S := Over.mk ((𝟙_ (Over T)).hom ≫ t)
    let et' : (Fin h ⊕ Fin h → ℤ) → (Tt ⟶ c₀.A) := fun a => pushHom pb' (𝟙_ (Over T)) (C'.lev a)
    have a' : ∀ a a₂, et' (a + a₂) = et' a * et' a₂ := fun a a₂ => by simp only [et', C'.lev_add, map_mul]
    have p' : ∀ a, et' a ^ N = 1 := fun a => by simp only [et', ← map_pow, C'.lev_tors, map_one]
    obtain ⟨u, hu, -⟩ := huniv Tt et' a' p'
    have hul : ∀ a, (u ≫ et a).left = (C'.lev a).left ≫ φ' := fun a => by rw [hu]; rfl
    have hut : u.left ≫ Z.hom = t := (Over.w u).trans (Category.id_comp t)
    have hulow : Set.range u.left ⊆ Ul := (HUl Tt u).1 fun a => by
      rw [MonObj.comp_pow, hu, comp_toUnit_assoc]
      apply Over.OverMorphism.ext
      simp only [et', ← map_pow]
      show (C'.lev a ^ (N / n)).left ≫ φ' = (toUnit Tt).left ≫ (c₀.lev a).left
      rw [low' a, pow_one, Over.toUnit_left]
      exact (Category.id_comp t ▸ rfl : t ≫ (c₀.lev a).left = Tt.hom ≫ (c₀.lev a).left)
    have huW : Set.range u.left ⊆ Wp := memWp Tt u fun k _ _ x a a₂ β hβ =>
      weilTransport h N n B' B' (b₀.ζ : B') (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' pb' hφ' k x β
        (Units.map β.toMonoidHom b.ζ) ((x ≫ u.left) ≫ Z.hom) _ _ a a₂
        (by rw [← hβ, Category.assoc, reassoc_of% hut])
        rfl (by rw [Category.assoc, hut])
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
    obtain ⟨t₁, ht₁⟩ := (Hi Tt u).1 fun _ hq => ⟨hulow hq, huW hq⟩
    have ht₁π : t₁.left ≫ V.hom = t := (Over.w t₁).trans (Category.id_comp t)
    refine ⟨t₁.left, ⟨ht₁π, (huniv' T t₁.left B' (b.ζ : B') (t ≫ s') C').2 ⟨φ', by rw [ht₁π]; exact ⟨pb', hφ', low'⟩,
      fun a => (hul a).symm.trans (by rw [← ht₁]; simp)⟩⟩, ?_⟩
    rintro t₂ ⟨ht₂, hpb₂⟩
    obtain ⟨φ₂, hsr₂, hl₂⟩ := (huniv' T t₂ B' (b.ζ : B') (t ≫ s') C').1 hpb₂
    rw [ht₂] at hsr₂
    have e := GlobalTheory.T.principal_siegel_object_odd_level_rigid h n N (N / n) B' B' b₀ (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' φ₂ hn hnodd hc₀
      ⟨pb', hφ', low'⟩ hsr₂
    subst e
    let h₂ : Tt ⟶ V := Over.homMk t₂ (ht₂.trans (Category.id_comp t).symm)
    have : h₂ ≫ i = u := R.ext fun a => Over.OverMorphism.ext (by rw [hul, hl₂ a]; simp [h₂])
    exact congrArg (fun q => q.left) ((cancel_mono i).1 (this.trans ht₁.symm))

end GlobalTheory.SiegCover
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  atlas_forward_decl GlobalTheory.SiegCover.exists_levelCover
end
