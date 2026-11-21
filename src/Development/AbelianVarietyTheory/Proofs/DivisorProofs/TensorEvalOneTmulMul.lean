import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverWithLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidCube
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_constant : GlobalTheory.AmpleRigid.ConstSt := by
  first | exact @GlobalTheory.AmpleRigid.constSt | exact GlobalTheory.AmpleRigid.constSt | (intros; apply GlobalTheory.AmpleRigid.constSt <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_cube : GlobalTheory.AmpleRigid.CubeSt := by
  first | exact @GlobalTheory.AmpleCube.cubeSt | exact GlobalTheory.AmpleCube.cubeSt | (intros; apply GlobalTheory.AmpleCube.cubeSt <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_finite_order : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  first | exact @GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | exact GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube | (intros; apply GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_separated : GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.SeparatedSt := by
  first | exact @GlobalTheory.AmpleRigid.separatedSt_of_const_cube | exact GlobalTheory.AmpleRigid.separatedSt_of_const_cube | (intros; apply GlobalTheory.AmpleRigid.separatedSt_of_const_cube <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_serre_ample : GlobalTheory.AmpleRigid.FiniteOrderSt → GlobalTheory.AmpleRigid.SeparatedSt → GlobalTheory.AmpleRigid.SerreAmpleSt := by
  first | exact @GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | exact GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated | (intros; apply GlobalTheory.AmpleRigid.serreAmple_of_finiteOrder_of_separated <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_rigid_level_rigid : GlobalTheory.AmpleRigid.SerreAmpleSt → GlobalTheory.AmpleRigid.LevelRigidSt := by
  first | exact @GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | exact GlobalTheory.AmpleRigid.levelRigid_of_serreAmple | (intros; apply GlobalTheory.AmpleRigid.levelRigid_of_serreAmple <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.LevelPow

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

theorem comp_act_natCast_mul (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    x ≫ X.rm.act ((k : 𝓞 F) * a) = (x ≫ X.rm.act a) ^ k := by
  induction k with
  | zero =>
    have h0 : X.rm.act 0 = 1 := by
      have h := X.rm.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.1 h.symm)
    rw [Nat.cast_zero, zero_mul, h0, pow_zero, MonObj.comp_one]
  | succ k ih =>
    rw [Nat.cast_succ, add_mul, _root_.one_mul, X.rm.add, MonObj.comp_mul, ih, pow_succ]

theorem pow_comp_act (X : Obj F 𝔠 S) {T : Over S} (x : T ⟶ X.A) (k : ℕ) (a : 𝓞 F) :
    (x ^ k) ≫ X.rm.act a = x ≫ X.rm.act ((k : 𝓞 F) * a) := by
  haveI := X.rm.hom a
  rw [MonObj.pow_comp, comp_act_natCast_mul]

theorem natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hn

theorem dvd_of_mul_dvd_mul {M M' : ℕ} (hM' : M' ≠ 0) {a : 𝓞 F}
    (h : ((M * M' : ℕ) : 𝓞 F) ∣ (M' : 𝓞 F) * a) : (M : 𝓞 F) ∣ a := by
  rw [Nat.cast_mul, mul_comm] at h
  exact (mul_dvd_mul_iff_left (natCast_ne_zero hM')).1 h

theorem exists_level_pow {X : Obj F 𝔠 S} {L M M' : ℕ} (hL : L = M * M') (hM : M ≠ 0) (hM' : M' ≠ 0)
    (ξ : X.Level L) : ∃ β : X.Level M, ∀ i, β.pt i = ξ.pt i ^ M' := by
  subst hL
  refine ⟨{ pt := fun i ↦ ξ.pt i ^ M', tors := ?_, inj := ?_, surj := ?_ }, fun _ ↦ rfl⟩
  · intro i
    rw [← pow_mul, mul_comm M' M, ξ.tors i]
  · intro Ω _ _ t a b h
    simp only [pow_comp_act] at h
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ h
    exact ⟨dvd_of_mul_dvd_mul hM' ha, dvd_of_mul_dvd_mul hM' hb⟩
  · intro Ω _ _ t y hy
    have hy' : y ^ (M * M') = 1 := by rw [pow_mul, hy, one_pow]
    obtain ⟨a, b, hab⟩ := ξ.surj Ω t y hy'
    have hN : (toUnit (Over.mk t) ≫ ξ.pt 0 ≫ X.rm.act ((M : 𝓞 F) * a)) *
        (toUnit (Over.mk t) ≫ ξ.pt 1 ≫ X.rm.act ((M : 𝓞 F) * b)) = 1 := by
      rw [← hy, hab, mul_pow]
      simp only [← Category.assoc, comp_act_natCast_mul, MonObj.comp_pow]
    obtain ⟨ha, hb⟩ := ξ.inj Ω t _ _ hN
    rw [mul_comm M M'] at ha hb
    obtain ⟨a', rfl⟩ := dvd_of_mul_dvd_mul hM ha
    obtain ⟨b', rfl⟩ := dvd_of_mul_dvd_mul hM hb
    refine ⟨a', b', ?_⟩
    rw [hab, pow_comp_act, pow_comp_act]

end GlobalTheory.RealMult.LevelPow

open GlobalTheory.RealMult.LevelPow in

theorem GlobalTheory.RealMult.Obj.Level.exists_pow_levels : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  intro F _ _ 𝔠 S X N N' hN hN' ξ
  exact ⟨exists_level_pow rfl hN hN' ξ, exists_level_pow (mul_comm N N') hN' hN ξ⟩
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_power_split : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.Level.exists_pow_levels
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

attribute [local instance] CategoryTheory.Hom.group CategoryTheory.Hom.commGroup

namespace GlobalTheory.RealMult.LevelComb

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

def actHom (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) :
    𝓞 F →+ Additive (T ⟶ X.A) :=
  AddMonoidHom.mk' (fun c ↦ Additive.ofMul (u ≫ z ≫ X.rm.act c)) (fun a b ↦ by
    simp only [X.rm.add, comp_mul]; rfl)

theorem comp_act_add (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (a b : 𝓞 F) :
    u ≫ z ≫ X.rm.act (a + b) = (u ≫ z ≫ X.rm.act a) * (u ≫ z ≫ X.rm.act b) := by
  simp only [X.rm.add, comp_mul]

theorem comp_act_zsmul (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (n : ℤ)
    (c : 𝓞 F) : u ≫ z ≫ X.rm.act (n • c) = (u ≫ z ≫ X.rm.act c) ^ n := by
  have h := map_zsmul (actHom X u z) n c
  exact congrArg Additive.toMul h

theorem comp_pow_act (X : Obj F 𝔠 S) {T : Over S} (u : T ⟶ 𝟙_ (Over S)) (z : 𝟙_ (Over S) ⟶ X.A) (m : ℕ)
    (c : 𝓞 F) : u ≫ (z ^ m) ≫ X.rm.act c = (u ≫ z ≫ X.rm.act c) ^ m := by
  haveI := X.rm.hom c
  rw [pow_comp, comp_pow]

end GlobalTheory.RealMult.LevelComb

open GlobalTheory.RealMult.LevelComb in

theorem GlobalTheory.RealMult.Obj.Level.comb : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  intro F _ _ 𝔠 S X N N' hc β β'
  obtain ⟨p, q, hpq⟩ : IsCoprime (N : ℤ) (N' : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  let pt : Fin 2 → (𝟙_ (Over S) ⟶ X.A) := fun i ↦ β.pt i ^ q * β'.pt i ^ p
  have h1 : ∀ i, pt i ^ N' = β.pt i := by
    intro i
    have hb : β.pt i ^ (q * (N' : ℤ)) = β.pt i := by
      rw [show q * (N' : ℤ) = 1 - (N : ℤ) * p by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β'.pt i ^ (p * (N' : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β'.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N' = β.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.mul_one]
  have h2 : ∀ i, pt i ^ N = β'.pt i := by
    intro i
    have hb : β'.pt i ^ (p * (N : ℤ)) = β'.pt i := by
      rw [show p * (N : ℤ) = 1 - (N' : ℤ) * q by linarith, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
        β'.tors i, one_zpow, inv_one, _root_.mul_one]
    have hb' : β.pt i ^ (q * (N : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, β.tors i, one_zpow]
    show (β.pt i ^ q * β'.pt i ^ p) ^ N = β'.pt i
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, hb, hb', _root_.one_mul]
  refine ⟨{ pt := pt, tors := ?_, inj := ?_, surj := ?_ }, h1, h2⟩
  · intro i
    rw [mul_comm, pow_mul, h1, β.tors]
  · intro Ω _ _ t a b h
    set u := toUnit (Over.mk t)
    have hβ : (u ≫ β.pt 0 ≫ X.rm.act a) * (u ≫ β.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h1, ← h1, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    have hβ' : (u ≫ β'.pt 0 ≫ X.rm.act a) * (u ≫ β'.pt 1 ≫ X.rm.act b) = 1 := by
      rw [← h2, ← h2, comp_pow_act, comp_pow_act, ← mul_pow, h, one_pow]
    obtain ⟨ha, hb⟩ := β.inj Ω t a b hβ
    obtain ⟨ha', hb'⟩ := β'.inj Ω t a b hβ'
    have hco : IsCoprime ((N : 𝓞 F)) ((N' : 𝓞 F)) := by
      simpa using (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
    rw [Nat.cast_mul]
    exact ⟨hco.mul_dvd ha ha', hco.mul_dvd hb hb'⟩
  · intro Ω _ _ t y hy
    set u := toUnit (Over.mk t)
    have hy1 : (y ^ N') ^ N = 1 := by rw [← pow_mul, mul_comm, hy]
    have hy2 : (y ^ N) ^ N' = 1 := by rw [← pow_mul, hy]
    obtain ⟨a, b, hab⟩ := β.surj Ω t (y ^ N') hy1
    obtain ⟨a', b', hab'⟩ := β'.surj Ω t (y ^ N) hy2
    rw [← h1, ← h1, comp_pow_act, comp_pow_act] at hab
    rw [← h2, ← h2, comp_pow_act, comp_pow_act] at hab'
    refine ⟨((N : ℤ) * p) • a' + ((N' : ℤ) * q) • a, ((N : ℤ) * p) • b' + ((N' : ℤ) * q) • b, ?_⟩
    rw [comp_act_add, comp_act_add, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul, comp_act_zsmul]
    have hy0 : y = y ^ ((N : ℤ) * p + (N' : ℤ) * q) := by
      rw [show (N : ℤ) * p + (N' : ℤ) * q = 1 by linarith, zpow_one]
    rw [hy0, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hab, hab', mul_zpow, mul_zpow,
      zpow_mul, zpow_mul, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
    exact mul_mul_mul_comm _ _ _ _

end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_crt_combine : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  atlas_forward_decl GlobalTheory.RealMult.Obj.Level.comb
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem tensorEval_includeRight_comp {R₀ A B : Type} [CommRing R₀] [CommRing A] [CommRing B] (ρ : A →+* B)
    (d : R₀ ⊗[ℤ] A) :
    tensorEval ((Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := B)).toRingHom.comp ρ) d =
      TensorProduct.comm ℤ B R₀
        (LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap (TensorProduct.comm ℤ R₀ A d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    simp [tensorEval_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isChartFun_unique : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {N : ℕ} {M : Scheme.{0}}
    {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens},
    IsDPModel N s U α V → ∀ {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}, Y.IsPullBy U hW.fromSpec φY →
    ∀ {δY : Y.DetGen} {h h' : R₀ ⊗[ℤ] Γ(M, W)}, IsChartFun r₀ Y δY h → IsChartFun r₀ Y δY h' → h = h' := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ W hW Y φY hY δY h h' hh hh'
  obtain ⟨-, -, hflat, hV, hnorm, hcod⟩ := hDP
  rw [← sub_eq_zero]
  have key := rTensor_eq_zero_of_restrict_affine_inf N M s V hflat hnorm hcod W hW R₀
    (TensorProduct.comm ℤ R₀ Γ(M, W) (h - h')) ?_
  · exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let ψ : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom.comp ρ
  obtain ⟨X, φ, hX⟩ := Obj.exists_isPullBy Y (spMap ψ)
  obtain ⟨δ, hδ, -⟩ := hX.existsUnique_detGen ψ δY

  have hmap : spMap ψ ≫ hW.fromSpec =
      spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom ≫ hW'.fromSpec := by
    rw [← hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op]
    simp [ψ, ρ, spMap, Spec.map_comp]
  have hXr : X.IsRapoport := by
    rw [Obj.isRapoport_iff]
    refine Set.eq_univ_of_forall fun x K _ t hx Z χ hZ ↦ ?_
    have hZU : Z.IsPullBy U (t ≫ spMap ψ ≫ hW.fromSpec) (χ ≫ φ ≫ φY) := hZ.comp (hX.comp hY)
    obtain ⟨z, rfl⟩ := hx
    have hmem : (t ≫ spMap ψ ≫ hW.fromSpec) z ∈ (V : Set M) := by
      rw [hmap]
      have : (hW'.fromSpec) ((t ≫ spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom) z) ∈ (W' : Set M) := by
        rw [← hW'.range_fromSpec]; exact ⟨_, rfl⟩
      exact (hle.trans inf_le_right) (by simpa using this)
    rw [hV] at hmem
    exact hmem K _ ⟨z, rfl⟩ Z _ hZU
  have e1 := hh _ ψ X φ hXr δ hX hδ
  have e2 := hh' _ ψ X φ hXr δ hX hδ
  have e : tensorEval ψ (h - h') = 0 := by rw [map_sub, ← e1, ← e2, sub_self]
  rw [tensorEval_includeRight_comp, LinearEquiv.map_eq_zero_iff] at e
  exact e

end GlobalTheory.RealMult
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_generator_pullback_rule : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {N : ℕ} {M : Scheme.{0}} {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens},
    IsDPModel N s U α V → ∀ {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}, Y.IsPullBy U hW.fromSpec φY →
    ∀ {δY : Y.DetGen} {h h' : R₀ ⊗[ℤ] Γ(M, W)}, IsChartFun r₀ Y δY h → IsChartFun r₀ Y δY h' → h = h' := by
  atlas_forward_decl GlobalTheory.RealMult.isChartFun_unique
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.RuleDescend
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ChartIndep

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

def tmap (R₀ : Type) [CommRing R₀] {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) : R₀ ⊗[ℤ] A →ₗ[ℤ] R₀ ⊗[ℤ] B :=
  LinearMap.lTensor R₀ ρ.toAddMonoidHom.toIntLinearMap

theorem tensorEval_tmap {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra R₀ R] (ρ : A →+* B)
    (ψ : B →+* R) (h : R₀ ⊗[ℤ] A) : tensorEval ψ (tmap R₀ ρ h) = tensorEval (ψ.comp ρ) h := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorEval_comp {A R R' : Type} [CommRing A] [CommRing R] [CommRing R'] [Algebra R₀ R] [Algebra R₀ R']
    (ψ : A →+* R) (σ : R →ₐ[R₀] R') (h : R₀ ⊗[ℤ] A) :
    tensorEval ((σ : R →+* R').comp ψ) h = σ (tensorEval ψ h) := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tensorEval_one_tmul_mul {A R : Type} [CommRing A] [CommRing R] [Algebra R₀ R] (ψ : A →+* R) (a : A)
    (h : R₀ ⊗[ℤ] A) : tensorEval ψ (((1 : R₀) ⊗ₜ[ℤ] a) * h) = ψ a * tensorEval ψ h := by
  induction h using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => rw [Algebra.TensorProduct.tmul_mul_tmul, tensorEval_tmul, tensorEval_tmul, _root_.one_mul, map_mul]; ring
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem isChartFun_pull {r₀ : Rule (rapObj 𝔠) R₀ k} {A B : Type} [CommRing A] [CommRing B] {ρ : A →+* B}
    {Y : Obj F 𝔠 (Sp A)} {Y' : Obj F 𝔠 (Sp B)} {κ : Y'.A.left ⟶ Y.A.left} (hκ : Y'.IsPullBy Y (spMap ρ) κ)
    {δ : Y.DetGen} {δ' : Y'.DetGen} (hd : Obj.DetCorr ρ κ δ.1 δ'.1) {h : R₀ ⊗[ℤ] A} (hh : IsChartFun r₀ Y δ h) :
    IsChartFun r₀ Y' δ' (tmap R₀ ρ h) := fun R _ _ ψ X φ hX ε hp he ↦ by
  rw [tensorEval_tmap]
  exact hh R _ X _ hX ε (isPullBy_comp hκ hp) (detCorr_comp hκ hp hd he)

theorem detCorr_smul {A R : Type} [CommRing A] [CommRing R] {ψ : A →+* R} {Y : Obj F 𝔠 (Sp A)}
    {X : Obj F 𝔠 (Sp R)} {φ : X.A.left ⟶ Y.A.left} {δ : Y.DetOmega} {ε : X.DetOmega}
    (hd : Obj.DetCorr ψ φ δ ε) (u : A) : Obj.DetCorr ψ φ (u • δ) (ψ u • ε) := fun v v' hv ↦ by
  change ψ u • ε v' = ψ (u • δ v)
  rw [hd v v' hv]
  simp

theorem exists_smul {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} (δ δ' : X.DetGen) : ∃ u : R, δ'.1 = u • δ.1 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : δ'.1 ∈ Submodule.span R {δ.1})
  exact ⟨a, ha.symm⟩

theorem eq_of_smul_gen {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)} (δ : X.DetGen) {u u' : R}
    (h : u • δ.1 = u' • δ.1) : u = u' := by
  haveI := X.invertible_detOmega
  refine eq_of_smul_eq_smul (α := X.DetOmega) fun m ↦ ?_
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 (δ.2.ge Submodule.mem_top : m ∈ Submodule.span R {δ.1})
  rw [smul_comm u, smul_comm u', h]

theorem isChartFun_smul {r₀ : Rule (rapObj 𝔠) R₀ k} {A : Type} [CommRing A] {Y : Obj F 𝔠 (Sp A)}
    {δ δ' : Y.DetGen} {u : A} (hu : δ'.1 = u • δ.1) {h : R₀ ⊗[ℤ] A} (hh : IsChartFun r₀ Y δ' h) :
    IsChartFun r₀ Y δ (((1 : R₀) ⊗ₜ[ℤ] (u ^ k)) * h) := fun R _ _ ψ X φ hX ε hp he ↦ by
  have hu' : IsUnit (ψ u) := (isUnit_of_eq_smul δ δ' u hu).map ψ
  let ε' : X.DetGen := ⟨ψ u • ε.1, (Submodule.span_singleton_smul_eq hu' _).trans ε.2⟩
  rw [tensorEval_one_tmul_mul, ← hh R ψ X φ hX ε' hp (hu ▸ detCorr_smul he u), map_pow]
  exact (r₀.homog R X hX ε ε' (ψ u) rfl).symm

theorem isPresVal_baseChange {A R R' : Type} [CommRing A] [CommRing R] [CommRing R'] [Algebra R₀ R] [Algebra R₀ R']
    (σ : R →ₐ[R₀] R') {Y : Obj F 𝔠 (Sp A)} {δY : Y.DetGen} {h : R₀ ⊗[ℤ] A} {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left} (hχ : X.IsPullBy Y (spMap ψ) χ) {v : R}
    (hv : IsPresVal k δY h δ ψ χ v) {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hφ : X'.IsPullBy X (spMap (σ : R →+* R')) φ) {δ' : X'.DetGen}
    (hd : Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1) :
    IsPresVal k δY h δ' ((σ : R →+* R').comp ψ) (φ ≫ χ) (σ v) := by
  intro ε' u' he' hu'
  obtain ⟨ε, he⟩ := (hχ.existsUnique_detGen ψ δY).exists
  obtain ⟨u, hu⟩ := exists_smul δ ε
  have hun : IsUnit (σ u) := (isUnit_of_eq_smul δ ε u hu).map σ
  let ε'' : X'.DetGen := ⟨σ u • δ'.1, (Submodule.span_singleton_smul_eq hun _).trans δ'.2⟩
  have h1 : Obj.DetCorr (σ : R →+* R') φ ε.1 ε''.1 := hu ▸ detCorr_smul hd u
  have h2 : ε' = ε'' := ((isPullBy_comp hχ hφ).existsUnique_detGen _ δY).unique he' (detCorr_comp hχ hφ he h1)
  have h3 : u' • δ'.1 = σ u • δ'.1 := hu'.symm.trans (congrArg Subtype.val h2)
  have h4 : u' = σ u := eq_of_smul_gen δ' h3
  rw [h4, tensorEval_comp, hv ε u he hu, map_mul, map_pow]

theorem exists_factor {R : Type} [CommRing R] [IsLocalRing R] {M : Scheme.{0}} (c : Sp R ⟶ M) {W : M.Opens}
    (hW : IsAffineOpen W) (h : c (IsLocalRing.closedPoint R) ∈ W) :
    ∃ ψ : Γ(M, W) →+* R, spMap ψ ≫ hW.fromSpec = c := by
  have hr : Set.range c ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map c.continuous).mem_open W.isOpen h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec c hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift hW.fromSpec c hr)).hom = IsOpenImmersion.lift hW.fromSpec c hr :=
    Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem spMap_injective {A R : Type} [CommRing A] [CommRing R] {ψ ψ' : A →+* R} (h : spMap ψ = spMap ψ') : ψ = ψ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_chart_detGen : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M) (y : M),
    ∃ (W : M.Opens) (hW : IsAffineOpen W), y ∈ W ∧ ∃ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ ∧ Nonempty Y.DetGen := by
  intro F _ _ 𝔠 M U y
  obtain ⟨W₀, hW₀, hyW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens) (show y ∈ (⊤ : M.Opens) from trivial)
  have hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y₀, φ₀, h₀⟩ := Obj.exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y₀
  let q := hW₀.primeIdealOf ⟨y, hyW₀⟩
  let p : Ideal Γ(M, W₀) := q.asIdeal
  haveI : p.IsPrime := q.isPrime
  haveI : Module.FinitePresentation Γ(M, W₀) Y₀.Lie := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Y₀.Lie) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨g, hg, hfree, hfr⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl Y₀.Lie) (Localization.AtPrime p)
  have hyW : y ∈ M.basicOpen g := by
    have h1 : q ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec q ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  have hW : IsAffineOpen (M.basicOpen g) := hW₀.basicOpen g
  letI : Algebra Γ(M, W₀) Γ(M, M.basicOpen g) := (M.presheaf.map (homOfLE (M.basicOpen_le g)).op).hom.toAlgebra
  haveI : IsLocalization.Away g Γ(M, M.basicOpen g) := hW₀.isLocalization_basicOpen g
  obtain ⟨Y, ψ, hψ⟩ := Obj.exists_isPullBy (S' := Sp Γ(M, M.basicOpen g)) Y₀
    (spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)))
  have hcomp : spMap (algebraMap Γ(M, W₀) Γ(M, M.basicOpen g)) ≫ hW₀.fromSpec = hW.fromSpec :=
    hW₀.map_fromSpec hW (homOfLE (M.basicOpen_le g)).op
  refine ⟨M.basicOpen g, hW, hyW, Y, ψ ≫ φ₀, by rw [← hcomp]; exact hψ.comp h₀, ?_⟩
  obtain ⟨e, -, -⟩ := Obj.exists_lieEquiv (R' := Γ(M, M.basicOpen g)) hψ
  haveI : Module.Finite (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers g) (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie)
  have hd : Module.finrank (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) = Module.finrank ℚ F := by
    rw [hfr]
    exact hrk q
  haveI : Nontrivial (Localization.Away g) :=
    (IsLocalization.Away.lift g (S := Localization.Away g) (g := algebraMap Γ(M, W₀) (Localization.AtPrime p))
      (IsLocalization.map_units (Localization.AtPrime p) ⟨g, hg⟩)).domain_nontrivial
  let b₀ := Module.finBasisOfFinrankEq (Localization.Away g) (LocalizedModule.Away g Y₀.Lie) hd
  haveI : IsLocalizedModule (Submonoid.powers g)
      (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Γ(M, M.basicOpen g) _).2
      (TensorProduct.isBaseChange _ _ _)
  let l := IsLocalizedModule.linearEquiv (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) Y₀.Lie) (TensorProduct.mk Γ(M, W₀) Γ(M, M.basicOpen g) Y₀.Lie 1)
  let τ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(M, M.basicOpen g)
  let Ψ := l.symm ≪≫ₗ b₀.repr.restrictScalars Γ(M, W₀) ≪≫ₗ Finsupp.mapRange.linearEquiv τ.toLinearEquiv
  let Ψ' := Ψ.extendScalarsOfIsLocalization (Submonoid.powers g) Γ(M, M.basicOpen g)
  exact ⟨Obj.DetGen.ofBasis Y ((Module.Basis.ofRepr Ψ').map e)⟩

theorem level_rigid : GlobalTheory.AmpleRigid.LevelRigidSt :=
  GlobalTheory.T.ample_rigid_level_rigid (GlobalTheory.T.ample_rigid_serre_ample (GlobalTheory.T.ample_rigid_finite_order GlobalTheory.T.ample_rigid_constant GlobalTheory.T.ample_rigid_cube) (GlobalTheory.T.ample_rigid_separated GlobalTheory.T.ample_rigid_constant GlobalTheory.T.ample_rigid_cube))

theorem exists_refine {r₀ : Rule (rapObj 𝔠) R₀ k} {M M₃ : Scheme.{0}} {U : Obj F 𝔠 M} {U₃ : Obj F 𝔠 M₃}
    {f : M₃ ⟶ M} {π : U₃.A.left ⟶ U.A.left} (hπ : U₃.IsPullBy U f π)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φ : Y.A.left ⟶ U.A.left}
    (hY : Y.IsPullBy U hW.fromSpec φ) {δY : Y.DetGen} {h : R₀ ⊗[ℤ] Γ(M, W)} (hh : IsChartFun r₀ Y δY h)
    {W₃ : M₃.Opens} (hW₃ : IsAffineOpen W₃) (hle : W₃ ≤ f ⁻¹ᵁ W) {Y₃ : Obj F 𝔠 (Sp Γ(M₃, W₃))}
    {φ₃ : Y₃.A.left ⟶ U₃.A.left} (hY₃ : Y₃.IsPullBy U₃ hW₃.fromSpec φ₃)
    {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {ψ : Γ(M, W) →+* R} {χ : X.A.left ⟶ Y.A.left} (hχ : X.IsPullBy Y (spMap ψ) χ)
    {ψ₃ : Γ(M₃, W₃) →+* R} {χ₃ : X.A.left ⟶ Y₃.A.left} (hχ₃ : X.IsPullBy Y₃ (spMap ψ₃) χ₃)
    (hb : spMap ψ ≫ hW.fromSpec = (spMap ψ₃ ≫ hW₃.fromSpec) ≫ f) (hτ : χ ≫ φ = (χ₃ ≫ φ₃) ≫ π)
    {v : R} (hv : IsPresVal k δY h δ ψ χ v) :
    ∃ (δ₃ : Y₃.DetGen) (h₃ : R₀ ⊗[ℤ] Γ(M₃, W₃)), IsChartFun r₀ Y₃ δ₃ h₃ ∧ IsPresVal k δ₃ h₃ δ ψ₃ χ₃ v := by
  let ρ : Γ(M, W) →+* Γ(M₃, W₃) := (f.appLE W W₃ hle).hom
  have hρ : hW₃.fromSpec ≫ f = spMap ρ ≫ hW.fromSpec := (hW.SpecMap_appLE_fromSpec f hW₃ hle).symm
  have h1 := hY₃.comp hπ
  rw [hρ] at h1
  obtain ⟨κ, hκ, hκφ⟩ := h1.cancel hY
  obtain rfl : ψ = ψ₃.comp ρ := spMap_injective (by
    rw [← cancel_mono hW.fromSpec, hb, RuleDescend.spMap_comp, Category.assoc, Category.assoc, hρ])
  obtain rfl : χ = χ₃ ≫ κ := hY.grp.1.hom_ext (by rw [hτ, Category.assoc, Category.assoc, hκφ])
    (by rw [hχ.grp.1.w, (isPullBy_comp hκ hχ₃).grp.1.w])
  obtain ⟨δ₃, hδ₃⟩ := (hκ.existsUnique_detGen ρ δY).exists
  refine ⟨δ₃, tmap R₀ ρ h, isChartFun_pull hκ hδ₃ hh, fun ε u he hu ↦ ?_⟩
  rw [tensorEval_tmap]
  exact hv ε u (detCorr_comp hκ hχ₃ hδ₃ he) hu

theorem eq_of_same_chart {r₀ : Rule (rapObj 𝔠) R₀ k} {N : ℕ} {M : Scheme.{0}}
    {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens}
    (hM : IsDPModel N s U α V) {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))}
    {φ : Y.A.left ⟶ U.A.left} (hY : Y.IsPullBy U hW.fromSpec φ) {δ₁ δ₂ : Y.DetGen} {h₁ h₂ : R₀ ⊗[ℤ] Γ(M, W)}
    (hh₁ : IsChartFun r₀ Y δ₁ h₁) (hh₂ : IsChartFun r₀ Y δ₂ h₂)
    {R : Type} [CommRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {ψ : Γ(M, W) →+* R} {χ : X.A.left ⟶ Y.A.left} (hχ : X.IsPullBy Y (spMap ψ) χ) {v₁ v₂ : R}
    (hv₁ : IsPresVal k δ₁ h₁ δ ψ χ v₁) (hv₂ : IsPresVal k δ₂ h₂ δ ψ χ v₂) : v₁ = v₂ := by
  obtain ⟨u, hu⟩ := exists_smul δ₁ δ₂
  obtain rfl := GlobalTheory.T.det_generator_pullback_rule hM r₀ hW hY hh₁ (isChartFun_smul hu hh₂)
  obtain ⟨ε, he⟩ := (hχ.existsUnique_detGen ψ δ₁).exists
  obtain ⟨w, hw⟩ := exists_smul δ ε
  have hu' : IsUnit (ψ u) := (isUnit_of_eq_smul δ₁ δ₂ u hu).map ψ
  let ε' : X.DetGen := ⟨ψ u • ε.1, (Submodule.span_singleton_smul_eq hu' _).trans ε.2⟩
  rw [hv₁ ε w he hw, hv₂ ε' (ψ u * w) (hu ▸ detCorr_smul he u) (by rw [mul_smul, ← hw]),
    tensorEval_one_tmul_mul, map_pow]
  ring

theorem mem_preimage {S M M₃ : Scheme.{0}} {W : M.Opens} (hW : IsAffineOpen W) {a : S ⟶ Spec Γ(M, W)} {c : S ⟶ M₃}
    {f : M₃ ⟶ M} (h : a ≫ hW.fromSpec = c ≫ f) (x : S) : c x ∈ f ⁻¹ᵁ W := by
  change f (c x) ∈ (W : Set M)
  rw [← Scheme.Hom.comp_apply, ← h, ← hW.range_fromSpec, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

theorem eq_of_model {r₀ : Rule (rapObj 𝔠) R₀ k} {N : ℕ} {M₃ : Scheme.{0}}
    {s : M₃ ⟶ Sp (Localization.Away (N : ℤ))} {U₃ : Obj F 𝔠 M₃} {α : U₃.Level N} {V : M₃.Opens}
    (hM : IsDPModel N s U₃ α V) {M₁ M₂ : Scheme.{0}} {U₁ : Obj F 𝔠 M₁} {U₂ : Obj F 𝔠 M₂}
    {f₁ : M₃ ⟶ M₁} {π₁ : U₃.A.left ⟶ U₁.A.left} (hπ₁ : U₃.IsPullBy U₁ f₁ π₁)
    {f₂ : M₃ ⟶ M₂} {π₂ : U₃.A.left ⟶ U₂.A.left} (hπ₂ : U₃.IsPullBy U₂ f₂ π₂)
    {W₁ : M₁.Opens} (hW₁ : IsAffineOpen W₁) {Y₁ : Obj F 𝔠 (Sp Γ(M₁, W₁))} {φ₁ : Y₁.A.left ⟶ U₁.A.left}
    (hY₁ : Y₁.IsPullBy U₁ hW₁.fromSpec φ₁) {δ₁ : Y₁.DetGen} {h₁ : R₀ ⊗[ℤ] Γ(M₁, W₁)} (hh₁ : IsChartFun r₀ Y₁ δ₁ h₁)
    {W₂ : M₂.Opens} (hW₂ : IsAffineOpen W₂) {Y₂ : Obj F 𝔠 (Sp Γ(M₂, W₂))} {φ₂ : Y₂.A.left ⟶ U₂.A.left}
    (hY₂ : Y₂.IsPullBy U₂ hW₂.fromSpec φ₂) {δ₂ : Y₂.DetGen} {h₂ : R₀ ⊗[ℤ] Γ(M₂, W₂)} (hh₂ : IsChartFun r₀ Y₂ δ₂ h₂)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {c : Sp R ⟶ M₃} {τ : X.A.left ⟶ U₃.A.left} (hτ : X.IsPullBy U₃ c τ)
    {ψ₁ : Γ(M₁, W₁) →+* R} {χ₁ : X.A.left ⟶ Y₁.A.left} (hχ₁ : X.IsPullBy Y₁ (spMap ψ₁) χ₁)
    {ψ₂ : Γ(M₂, W₂) →+* R} {χ₂ : X.A.left ⟶ Y₂.A.left} (hχ₂ : X.IsPullBy Y₂ (spMap ψ₂) χ₂)
    (hb₁ : spMap ψ₁ ≫ hW₁.fromSpec = c ≫ f₁) (hτ₁ : χ₁ ≫ φ₁ = τ ≫ π₁)
    (hb₂ : spMap ψ₂ ≫ hW₂.fromSpec = c ≫ f₂) (hτ₂ : χ₂ ≫ φ₂ = τ ≫ π₂)
    {v₁ v₂ : R} (hv₁ : IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁) (hv₂ : IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂) : v₁ = v₂ := by
  have m₁ := mem_preimage hW₁ hb₁ (IsLocalRing.closedPoint R)
  have m₂ := mem_preimage hW₂ hb₂ (IsLocalRing.closedPoint R)
  obtain ⟨_, ⟨W₃, hW₃, rfl⟩, hm, hle⟩ := M₃.isBasis_affineOpens.exists_subset_of_mem_open
    (show c (IsLocalRing.closedPoint R) ∈ ((f₁ ⁻¹ᵁ W₁ ⊓ f₂ ⁻¹ᵁ W₂ : M₃.Opens) : Set M₃) from ⟨m₁, m₂⟩)
    (f₁ ⁻¹ᵁ W₁ ⊓ f₂ ⁻¹ᵁ W₂).isOpen
  have hle' : W₃ ≤ f₁ ⁻¹ᵁ W₁ ⊓ f₂ ⁻¹ᵁ W₂ := hle
  replace hW₃ : IsAffineOpen W₃ := hW₃
  obtain ⟨ψ₃, rfl⟩ := exists_factor c hW₃ hm
  obtain ⟨Y₃, φ₃, hY₃⟩ := U₃.exists_isPullBy hW₃.fromSpec
  obtain ⟨χ₃, hχ₃, rfl⟩ := hτ.cancel hY₃
  obtain ⟨ε₁, g₁, hg₁, hw₁⟩ := exists_refine hπ₁ hW₁ hY₁ hh₁ hW₃ (hle'.trans inf_le_left) hY₃ hχ₁ hχ₃ hb₁ hτ₁ hv₁
  obtain ⟨ε₂, g₂, hg₂, hw₂⟩ := exists_refine hπ₂ hW₂ hY₂ hh₂ hW₃ (hle'.trans inf_le_right) hY₃ hχ₂ hχ₃ hb₂ hτ₂ hv₂
  exact eq_of_same_chart hM hW₃ hY₃ hg₁ hg₂ hχ₃ hw₁ hw₂

theorem hom_away_ext {S : Scheme.{0}} {N : ℕ} (t t' : S ⟶ Sp (Localization.Away (N : ℤ))) : t = t' := by
  rw [← cancel_mono (spMap (algebraMap ℤ (Localization.Away (N : ℤ))))]
  exact specZIsTerminal.hom_ext _ _

theorem exists_hom_away {R : Type} [CommRing R] {N : ℕ} (h : IsUnit (N : R)) :
    Nonempty (Sp R ⟶ Sp (Localization.Away (N : ℤ))) :=
  ⟨spMap (IsLocalization.Away.lift (N : ℤ) (g := Int.castRingHom R) (by simpa using h))⟩

theorem isUnit_of_hom_away {R : Type} [CommRing R] {N : ℕ} (t : Sp R ⟶ Sp (Localization.Away (N : ℤ))) :
    IsUnit (N : R) := by
  have := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (N : ℤ)) (N : ℤ)).map (Spec.preimage t).hom
  simpa using this

theorem eq_of_level {N : ℕ} (hN : 3 ≤ N) {M : Scheme.{0}} {s : M ⟶ Sp (Localization.Away (N : ℤ))}
    {U : Obj F 𝔠 M} {α : U.Level N} (hM : IsFineModuli s α) {R : Type} [CommRing R] {X : Obj F 𝔠 (Sp R)}
    (β : X.Level N) {b b' : Sp R ⟶ M} {τ τ' : X.A.left ⟶ U.A.left} (h : X.IsPullBy U b τ) (h' : X.IsPullBy U b' τ')
    (e : ∀ i, (β.pt i).left ≫ τ = b ≫ (α.pt i).left) (e' : ∀ i, (β.pt i).left ≫ τ' = b' ≫ (α.pt i).left) :
    b = b' ∧ τ = τ' := by
  obtain rfl : b = b' := (hM _ (b ≫ s) X β).unique ⟨rfl, τ, h, e⟩ ⟨hom_away_ext _ _, τ', h', e'⟩
  refine ⟨rfl, ?_⟩
  have h₁ : X.IsPullBy U (𝟙 _ ≫ b) τ := by rwa [Category.id_comp]
  obtain ⟨g, hg, rfl⟩ := h₁.cancel h'
  rw [level_rigid F 𝔠 N hN R (isUnit_of_hom_away (b ≫ s)) X β g hg fun i ↦ ?_, Category.id_comp]
  refine h'.grp.1.hom_ext (by rw [Category.assoc, e, e']) ?_
  rw [Category.assoc, hg.grp.1.w, Category.comp_id]

theorem pow_left_comp {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X b φ) {x : 𝟙_ (Over S) ⟶ X.A} {x' : 𝟙_ (Over S') ⟶ X'.A}
    (e : x'.left ≫ φ = b ≫ x.left) (n : ℕ) : (x' ^ n).left ≫ φ = b ≫ (x ^ n).left := by
  have e₁ : pushPt h.grp.1.w x' = toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ b)) ≫ x := by
    apply Over.OverMorphism.ext
    change x'.left ≫ φ = _
    rw [e, Over.comp_left, LevelPull.toUnit_left]
    simp
  have e₂ := congrArg (fun z ↦ z.left) (LevelPull.push_pow h.grp x' n)
  rw [e₁, ← MonObj.comp_pow] at e₂
  refine Eq.trans e₂ ?_
  rw [Over.comp_left, LevelPull.toUnit_left]
  simp

theorem eq_of_coprime [IsTotallyReal F] (hDP : GlobalTheory.Published.DelignePappasModel) {r₀ : Rule (rapObj 𝔠) R₀ k} {N p : ℕ}
    (hN : 3 ≤ N) (hp : 3 ≤ p) (hc : Nat.Coprime N p)
    {M₁ : Scheme.{0}} {s₁ : M₁ ⟶ Sp (Localization.Away (N : ℤ))} {U₁ : Obj F 𝔠 M₁} {α₁ : U₁.Level N}
    (hM₁ : IsFineModuli s₁ α₁)
    {M₂ : Scheme.{0}} {s₂ : M₂ ⟶ Sp (Localization.Away (p : ℤ))} {U₂ : Obj F 𝔠 M₂} {α₂ : U₂.Level p}
    (hM₂ : IsFineModuli s₂ α₂)
    {W₁ : M₁.Opens} (hW₁ : IsAffineOpen W₁) {Y₁ : Obj F 𝔠 (Sp Γ(M₁, W₁))} {φ₁ : Y₁.A.left ⟶ U₁.A.left}
    (hY₁ : Y₁.IsPullBy U₁ hW₁.fromSpec φ₁) {δ₁ : Y₁.DetGen} {h₁ : R₀ ⊗[ℤ] Γ(M₁, W₁)} (hh₁ : IsChartFun r₀ Y₁ δ₁ h₁)
    {W₂ : M₂.Opens} (hW₂ : IsAffineOpen W₂) {Y₂ : Obj F 𝔠 (Sp Γ(M₂, W₂))} {φ₂ : Y₂.A.left ⟶ U₂.A.left}
    (hY₂ : Y₂.IsPullBy U₂ hW₂.fromSpec φ₂) {δ₂ : Y₂.DetGen} {h₂ : R₀ ⊗[ℤ] Γ(M₂, W₂)} (hh₂ : IsChartFun r₀ Y₂ δ₂ h₂)
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra R₀ R] {X : Obj F 𝔠 (Sp R)} {δ : X.DetGen}
    {ψ₁ : Γ(M₁, W₁) →+* R} {χ₁ : X.A.left ⟶ Y₁.A.left} (hχ₁ : X.IsPullBy Y₁ (spMap ψ₁) χ₁)
    {ψ₂ : Γ(M₂, W₂) →+* R} {χ₂ : X.A.left ⟶ Y₂.A.left} (hχ₂ : X.IsPullBy Y₂ (spMap ψ₂) χ₂)
    {v₁ v₂ : R} (hv₁ : IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁) (hv₂ : IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂) : v₁ = v₂ := by
  have hτ₁ := hχ₁.comp hY₁
  have hτ₂ := hχ₂.comp hY₂
  obtain ⟨β₁, hβ₁⟩ := LevelPull.exists_level_pull hτ₁ α₁
  obtain ⟨β₂, hβ₂⟩ := LevelPull.exists_level_pull hτ₂ α₂
  obtain ⟨ξ, hξ₁, hξ₂⟩ := GlobalTheory.T.level_structure_crt_combine hc β₁ β₂
  obtain ⟨M₃, s₃, U₃, α₃, V₃, hM₃⟩ := exists_isDPModel hDP F 𝔠 (N * p) (by nlinarith)
  have hu : IsUnit ((N * p : ℕ) : R) := by
    rw [Nat.cast_mul]
    exact (isUnit_of_hom_away ((spMap ψ₁ ≫ hW₁.fromSpec) ≫ s₁)).mul (isUnit_of_hom_away ((spMap ψ₂ ≫ hW₂.fromSpec) ≫ s₂))
  obtain ⟨t⟩ := exists_hom_away hu
  obtain ⟨c, -, τ, hτ, hτξ⟩ := (hM₃.1 _ t X ξ).exists
  obtain ⟨⟨a₁, ha₁⟩, a₂, ha₂⟩ := GlobalTheory.T.level_structure_power_split (by omega) (by omega) α₃
  have hu₃ : IsUnit ((N : Localization.Away ((N * p : ℕ) : ℤ)) * (p : Localization.Away ((N * p : ℕ) : ℤ))) :=
    (Nat.cast_mul (α := Localization.Away ((N * p : ℕ) : ℤ)) N p).symm ▸ isUnit_of_hom_away (𝟙 _)
  obtain ⟨t₁⟩ := exists_hom_away (isUnit_of_mul_isUnit_left hu₃)
  obtain ⟨t₂⟩ := exists_hom_away (isUnit_of_mul_isUnit_right hu₃)
  obtain ⟨f₁, -, π₁, hπ₁, hf₁⟩ := (hM₁ _ (s₃ ≫ t₁) U₃ a₁).exists
  obtain ⟨f₂, -, π₂, hπ₂, hf₂⟩ := (hM₂ _ (s₃ ≫ t₂) U₃ a₂).exists
  obtain ⟨e₁, e₁'⟩ := eq_of_level hN hM₁ β₁ hτ₁ (hτ.comp hπ₁) hβ₁ fun i ↦ by
    rw [← hξ₁, ← Category.assoc, pow_left_comp hτ (hτξ i), ← ha₁, Category.assoc, hf₁, Category.assoc]
  obtain ⟨e₂, e₂'⟩ := eq_of_level hp hM₂ β₂ hτ₂ (hτ.comp hπ₂) hβ₂ fun i ↦ by
    rw [← hξ₂, ← Category.assoc, pow_left_comp hτ (hτξ i), ← ha₂, Category.assoc, hf₂, Category.assoc]
  exact eq_of_model hM₃ hπ₁ hπ₂ hW₁ hY₁ hh₁ hW₂ hY₂ hh₂ hτ hχ₁ hχ₂ e₁ e₁' e₂ e₂' hv₁ hv₂

theorem exists_isPresVal {A R : Type} [CommRing A] [CommRing R] [Algebra R₀ R] {Y : Obj F 𝔠 (Sp A)} (δY : Y.DetGen)
    (h : R₀ ⊗[ℤ] A) {X : Obj F 𝔠 (Sp R)} (δ : X.DetGen) {ψ : A →+* R} {χ : X.A.left ⟶ Y.A.left}
    (hχ : X.IsPullBy Y (spMap ψ) χ) : ∃ v, IsPresVal k δY h δ ψ χ v := by
  obtain ⟨ε, he, hu⟩ := hχ.existsUnique_detGen ψ δY
  obtain ⟨u, hεu⟩ := exists_smul δ ε
  refine ⟨u ^ k * tensorEval ψ h, fun ε' u' he' hu' ↦ ?_⟩
  obtain rfl := hu ε' he'
  rw [eq_of_smul_gen δ (hu'.symm.trans hεu)]

theorem exists_local_level [IsTotallyReal F] {N : ℕ} (hN : N ≠ 0) {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (x : R)
    (hx : x ≠ 0) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R'))
      (φ : X'.A.left ⟶ X.A.left) (p : ℕ), σ x ≠ 0 ∧ X'.IsPullBy X (spMap σ) φ ∧ 3 ≤ p ∧ Nat.Coprime N p ∧
      IsUnit (p : R') ∧ Nonempty (X'.Level p) := by
  have loc : ∀ {A : Type} [CommRing A] (y : A), y ≠ 0 → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B)
      (σ : A →+* B), σ y ≠ 0 := fun {A} _ y hy ↦ by
    by_contra H
    refine hy (eq_zero_of_localization y fun J hJ ↦ ?_)
    by_contra h
    exact H ⟨Localization.AtPrime J, inferInstance, inferInstance, algebraMap _ _, h⟩
  obtain ⟨R₁, _, _, σ₁, h₁⟩ := loc x hx
  obtain ⟨p, hp3, hc, hu⟩ : ∃ p : ℕ, 3 ≤ p ∧ Nat.Coprime N p ∧ IsUnit (p : R₁) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
      (a := ((2 * N * (2 * N + 1) + 1 : ℕ) : R₁)) (b := -((2 * N * (2 * N + 1) : ℕ) : R₁)) (by simp) with h | h
    · refine ⟨_, by nlinarith [Nat.pos_of_ne_zero hN], ?_, h⟩
      rw [show 2 * N * (2 * N + 1) + 1 = 1 + N * (2 * (2 * N + 1)) by ring]
      simp
    · rw [IsUnit.neg_iff, Nat.cast_mul] at h
      refine ⟨_, by omega, ?_, isUnit_of_mul_isUnit_right h⟩
      rw [show 2 * N + 1 = 1 + N * 2 by ring]
      simp
  obtain ⟨X₁, φ₁, k₁⟩ := X.exists_isPullBy (spMap σ₁)
  obtain ⟨R₂, _, σ₂, X₂, φ₂, hσ₂, k₂, ⟨β⟩⟩ := exists_faithfullyFlat_level F 𝔠 p (by omega) R₁ hu X₁
  obtain ⟨R₃, _, _, σ₃, h₃⟩ := loc (σ₂ (σ₁ x)) fun h ↦ h₁ (hσ₂.injective (h.trans (map_zero σ₂).symm))
  obtain ⟨X₃, φ₃, k₃⟩ := X₂.exists_isPullBy (spMap σ₃)
  obtain ⟨β', -⟩ := k₃.exists_level β
  exact ⟨R₃, inferInstance, inferInstance, σ₃.comp (σ₂.comp σ₁), X₃, _, p, h₃, isPullBy_comp (isPullBy_comp k₁ k₂) k₃,
    hp3, hc, by simpa using hu.map (σ₃.comp σ₂), ⟨β'⟩⟩

theorem presVal_indep : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
  (N : ℕ), 3 ≤ N → ∀ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (α : U.Level N)
  (V : M.Opens), IsDPModel N s U α V →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k),
  (∀ (N' : ℕ) (M' : Scheme.{0}) (s' : M' ⟶ Sp (Localization.Away (N' : ℤ))) (U' : Obj F 𝔠 M') (α' : U'.Level N')
    (V' : M'.Opens), 3 ≤ N' → IsDPModel N' s' U' α' V' → (∀ (W : M'.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M', W))) (φY : Y.A.left ⟶ U'.A.left),
    Y.IsPullBy U' hW.fromSpec φY → ∀ δY : Y.DetGen, ∃ h : R₀ ⊗[ℤ] Γ(M', W), IsChartFun r₀ Y δY h)) →
  (∀ (W₁ : M.Opens) (hW₁ : IsAffineOpen W₁) (Y₁ : Obj F 𝔠 (Sp Γ(M, W₁))) (φ₁ : Y₁.A.left ⟶ U.A.left),
    Y₁.IsPullBy U hW₁.fromSpec φ₁ → ∀ (δ₁ : Y₁.DetGen) (h₁ : R₀ ⊗[ℤ] Γ(M, W₁)), IsChartFun r₀ Y₁ δ₁ h₁ →
  ∀ (W₂ : M.Opens) (hW₂ : IsAffineOpen W₂) (Y₂ : Obj F 𝔠 (Sp Γ(M, W₂))) (φ₂ : Y₂.A.left ⟶ U.A.left),
    Y₂.IsPullBy U hW₂.fromSpec φ₂ → ∀ (δ₂ : Y₂.DetGen) (h₂ : R₀ ⊗[ℤ] Γ(M, W₂)), IsChartFun r₀ Y₂ δ₂ h₂ →
  ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (ψ₁ : Γ(M, W₁) →+* R) (χ₁ : X.A.left ⟶ Y₁.A.left) (ψ₂ : Γ(M, W₂) →+* R) (χ₂ : X.A.left ⟶ Y₂.A.left),
    X.IsPullBy Y₁ (spMap ψ₁) χ₁ → X.IsPullBy Y₂ (spMap ψ₂) χ₂ →
    ∀ v₁ v₂ : R, IsPresVal k δ₁ h₁ δ ψ₁ χ₁ v₁ → IsPresVal k δ₂ h₂ δ ψ₂ χ₂ v₂ → v₁ = v₂) := by
  intro hDP F _ _ _ 𝔠 N hN M s U α V hM R₀ _ k r₀ H W₁ hW₁ Y₁ φ₁ hY₁ δ₁ h₁ hh₁ W₂ hW₂ Y₂ φ₂ hY₂ δ₂ h₂ hh₂
    R _ _ X δ ψ₁ χ₁ ψ₂ χ₂ hχ₁ hχ₂ v₁ v₂ hv₁ hv₂
  by_contra hne
  obtain ⟨R', _, _, σ, X', φ, p, hσ, hφ, hp, hc, hu, ⟨β⟩⟩ := exists_local_level (N := N) (by omega) X _ (sub_ne_zero.2 hne)
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σ' : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  obtain ⟨δ', hδ'⟩ := (hφ.existsUnique_detGen σ δ).exists
  have w₁ := isPresVal_baseChange σ' hχ₁ hv₁ hφ hδ'
  have w₂ := isPresVal_baseChange σ' hχ₂ hv₂ hφ hδ'
  obtain ⟨M', s', U', α', V', hM'⟩ := exists_isDPModel hDP F 𝔠 p hp
  obtain ⟨t⟩ := exists_hom_away hu
  obtain ⟨c, -, τ, hτ, -⟩ := (hM'.1 _ t X' β).exists
  obtain ⟨W', hW', hm, Y', φ', hY', ⟨δY⟩⟩ := exists_chart_detGen F 𝔠 M' U' (c (IsLocalRing.closedPoint R'))
  obtain ⟨h', hh'⟩ := H p M' s' U' α' V' hp hM' W' hW' Y' φ' hY' δY
  obtain ⟨ψ', rfl⟩ := exists_factor c hW' hm
  obtain ⟨χ', hχ', -⟩ := hτ.cancel hY'
  obtain ⟨v', hv'⟩ := exists_isPresVal (k := k) δY h' δ' hχ'
  have e₁ := eq_of_coprime hDP hN hp hc hM.1 hM'.1 hW₁ hY₁ hh₁ hW' hY' hh' (isPullBy_comp hχ₁ hφ) hχ' w₁ hv'
  have e₂ := eq_of_coprime hDP hN hp hc hM.1 hM'.1 hW₂ hY₂ hh₂ hW' hY' hh' (isPullBy_comp hχ₂ hφ) hχ' w₂ hv'
  exact hσ (by rw [map_sub]; exact sub_eq_zero.2 (e₁.trans e₂.symm))

end GlobalTheory.RealMult.ChartIndep
end
end
