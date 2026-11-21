import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesNatural
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalIdealMul
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)
  {P P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}

structure CechFamily (P P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) where

  φ : ∀ {n : ℕ} (i : Fin (n + 1) → ι), P.obj (op (inter U i)) →+ P'.obj (op (inter U i))

  res_comm : ∀ {m n : ℕ} (i : Fin (m + 1) → ι) (j : Fin (n + 1) → ι) (h : inter U i ≤ inter U j)
    (x : P.obj (op (inter U j))), φ i (res P h x) = res P' h (φ j x)

namespace CechFamily

variable {U}

noncomputable section

def cochain (Φ : CechFamily U P P') (n : ℕ) : Cochain P U n →+ Cochain P' U n where
  toFun σ i := Φ.φ i (σ i)
  map_zero' := by
    funext i
    exact map_zero _
  map_add' σ τ := by
    funext i
    exact map_add _ _ _

lemma cochain_apply (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    Φ.cochain n σ i = Φ.φ i (σ i) := rfl

lemma cochain_d (Φ : CechFamily U P P') (n : ℕ) (σ : Cochain P U n) :
    Φ.cochain (n + 1) (d P U n σ) = d P' U n (Φ.cochain n σ) := by
  funext i
  rw [cochain_apply, d_apply, d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Φ.res_comm]
  rfl

lemma cochain_mem_cocycles (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ cocycles P U n) : Φ.cochain n σ ∈ cocycles P' U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← cochain_d, hσ, map_zero]

lemma cochain_mem_coboundaries (Φ : CechFamily U P P') {n : ℕ} {σ : Cochain P U n}
    (hσ : σ ∈ coboundaries P U n) : Φ.cochain n σ ∈ coboundaries P' U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨Φ.cochain n τ, (cochain_d Φ n τ).symm⟩

def cocycles (Φ : CechFamily U P P') (n : ℕ) : cocycles P U n →+ GroundTheory.Arith.SchemeCoh.cocycles P' U n :=
  AddMonoidHom.codRestrict ((Φ.cochain n).comp (GroundTheory.Arith.SchemeCoh.cocycles P U n).subtype) _
    fun σ => cochain_mem_cocycles Φ σ.2

def cechH (Φ : CechFamily U P P') (n : ℕ) : GroundTheory.Arith.SchemeCoh.cechH P U n →+
    GroundTheory.Arith.SchemeCoh.cechH P' U n :=
  QuotientAddGroup.map _ _ (Φ.cocycles n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact cochain_mem_coboundaries Φ (AddSubgroup.mem_addSubgroupOf.1 hσ)

lemma cechH_cls (Φ : CechFamily U P P') {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    Φ.cechH n (cls σ hσ) = cls (Φ.cochain n σ) (by rw [← cochain_d, hσ, map_zero]) := rfl

def ofHom (f : P ⟶ P') : CechFamily U P P' where
  φ i := (f.app (op (inter U i))).hom
  res_comm i j h x := app_res f h x

lemma ofHom_cechH (f : P ⟶ P') (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (ofHom (U := U) f).cechH n x = cechHMap U f n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rfl

def comp (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') : CechFamily U P P'' where
  φ i := (Ψ.φ i).comp (Φ.φ i)
  res_comm i j h x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [Φ.res_comm, Ψ.res_comm]

lemma comp_cechH (Φ : CechFamily U P P') (Ψ : CechFamily U P' P'') (n : ℕ)
    (x : GroundTheory.Arith.SchemeCoh.cechH P U n) :
    (Φ.comp Ψ).cechH n x = Ψ.cechH n (Φ.cechH n x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rfl

def add (Φ Ψ : CechFamily U P P') : CechFamily U P P' where
  φ i := Φ.φ i + Ψ.φ i
  res_comm i j h x := by
    simp only [AddMonoidHom.add_apply, map_add]
    rw [Φ.res_comm, Ψ.res_comm]


lemma cechH_congr {Φ Ψ : CechFamily U P P'} (h : ∀ {n : ℕ} (i : Fin (n + 1) → ι) x, Φ.φ i x = Ψ.φ i x)
    (n : ℕ) (x : GroundTheory.Arith.SchemeCoh.cechH P U n) : Φ.cechH n x = Ψ.cechH n x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechH_cls, cechH_cls]
  exact cls_congr U (by funext i; exact h i _) _ _

end

end CechFamily

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

omit [IsNoetherianRing A] in
lemma algV_eq_toFunctions (V : X.Opens) (a : A) : algV X V a = toFunctions V a := rfl

def powSmulTopΓ (V : X.Opens) (n : ℕ) : Submodule Γ(X, V) Γ(F, V) where
  carrier := (I ^ n • ⊤ : Submodule A Γ(F, V))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
    · change c • (a • y) ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [sectionsModuleA_smul, smul_smul, mul_comm, ← smul_smul, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    · rw [smul_add]
      exact add_mem hy hz

lemma mem_pow_smul_top_iff {V : X.Opens} (n : ℕ) (m : Γ(F, V)) :
    m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) ↔
      m ∈ (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) := by
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun a ha x _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [sectionsModuleA_smul, algV_eq_toFunctions]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial
  · intro hm
    have h : I ^ n ≤ ((powSmulTopΓ (F := F) I V n).colon (Set.univ)).comap (toFunctions V) := by
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon]
      intro x _
      change toFunctions V a • x ∈ (I ^ n • ⊤ : Submodule A Γ(F, V))
      rw [← algV_eq_toFunctions, ← sectionsModuleA_smul]
      exact Submodule.smul_mem_smul ha trivial
    have h' := Ideal.map_le_iff_le_comap.2 h
    have : (Ideal.map (toFunctions V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ(F, V)) ≤
        powSmulTopΓ I V n :=
      Submodule.smul_le.2 fun c hc x _ => Submodule.mem_colon.1 (h' hc) x trivial
    exact this hm

variable [F.IsQuasicoherent]

lemma mem_range_idealPowι_iff {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ) (m : Γ(F, V)) :
    m ∈ Set.range ((idealPowι I F n).app V) ↔ m ∈ (I ^ n • ⊤ : Submodule A Γ(F, V)) := by
  rw [range_idealPowι_app I F hV n, mem_pow_smul_top_iff]
  rfl

variable (hF : IsCoherent F)

section Sections

variable {V : X.Opens} (hV : IsAffineOpen V)

def reesCoef (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(F, V) where
  toFun s := (reesSectionsMap I hF hV s).coeff n
  map_zero' := by rw [reesSectionsMap_zero]; rfl
  map_add' s s' := by rw [reesSectionsMap_add]; rfl

lemma reesCoef_mem (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV n s ∈ Set.range ((idealPowι I F n).app V) :=
  (mem_range_idealPowι_iff I hV n _).2 ((mem_reesSubmodule_iff.1 (reesSectionsMap_mem hF hV s)) n)

lemma idealPowι_app_injective (n : ℕ) : Function.Injective ((idealPowι I F n).app V) :=
  kernel_ι_app_injective _ V

def reesDeg (n : ℕ) : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) →+ Γ(idealPow I F n, V) where
  toFun s := (Equiv.ofInjective _ (idealPowι_app_injective I n)).symm
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩
  map_zero' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n 0 = _
    rw [map_zero, map_zero]
  map_add' s s' := by
    apply idealPowι_app_injective I n
    refine (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n) _).trans ?_
    change reesCoef I hF hV n (s + s') = _
    rw [map_add, map_add]
    congr 1
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩).symm
    · exact (Equiv.apply_ofInjective_symm (idealPowι_app_injective (F := F) (V := V) I n)
        ⟨reesCoef I hF hV n s', reesCoef_mem I hF hV n s'⟩).symm

lemma idealPowι_reesDeg (n : ℕ) (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (idealPowι I F n).app V (reesDeg I hF hV n s) = reesCoef I hF hV n s :=
  Equiv.apply_ofInjective_symm (idealPowι_app_injective I n)
    ⟨reesCoef I hF hV n s, reesCoef_mem I hF hV n s⟩

include hV in
lemma lsingle_mem_reesSubmodule (n : ℕ) (g : Γ(idealPow I F n, V)) :
    PolynomialModule.lsingle A n ((idealPowι I F n).app V g) ∈ reesSubmodule I Γ(F, V) := by
  rw [mem_reesSubmodule_iff]
  intro k
  rw [PolynomialModule.lsingle_apply]
  split_ifs with h
  · subst h
    exact (mem_range_idealPowι_iff I hV n _).1 ⟨g, rfl⟩
  · exact zero_mem _

include hF hV in

def reesInc (n : ℕ) : Γ(idealPow I F n, V) →+ Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V) :=
  (reesSectionsEquiv I hF hV).symm.toAddMonoidHom.comp
    (AddMonoidHom.codRestrict
      ((PolynomialModule.lsingle A n).toAddMonoidHom.comp ((idealPowι I F n).app V).hom)
      (reesSubmodule I Γ(F, V)).toAddSubmonoid (lsingle_mem_reesSubmodule I hV n))

lemma reesSectionsMap_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesSectionsMap I hF hV (reesInc I hF hV n g) =
      PolynomialModule.lsingle A n ((idealPowι I F n).app V g) := by
  rw [← reesSectionsEquiv_apply]
  change ((reesSectionsEquiv I hF hV ((reesSectionsEquiv I hF hV).symm _)) :
    PolynomialModule A Γ(F, V)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

lemma reesCoef_reesInc (n k : ℕ) (g : Γ(idealPow I F n, V)) :
    reesCoef I hF hV k (reesInc I hF hV n g) = if n = k then (idealPowι I F n).app V g else 0 := by
  change (reesSectionsMap I hF hV (reesInc I hF hV n g)).coeff k = _
  rw [reesSectionsMap_reesInc, PolynomialModule.lsingle_apply]

lemma reesDeg_reesInc (n : ℕ) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV n (reesInc I hF hV n g) = g := by
  apply idealPowι_app_injective I n
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_pos rfl]

lemma reesDeg_reesInc_of_ne {n k : ℕ} (h : n ≠ k) (g : Γ(idealPow I F n, V)) :
    reesDeg I hF hV k (reesInc I hF hV n g) = 0 := by
  apply idealPowι_app_injective I k
  rw [idealPowι_reesDeg, reesCoef_reesInc, if_neg h, map_zero]

end Sections

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe w u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} [X.Over (Spec (.of A))]
  (F : X.Modules)

abbrev reesPush : X.Modules := (Scheme.Modules.pushforward (reesPr I X)).obj (reesSheaf I F)

def reesMul (r : reesAlgebra I) : reesPush I F ⟶ reesPush I F :=
  (Scheme.Modules.pushforward (reesPr I X)).map
    (smulHom (reesSheaf I F) (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))

lemma reesMul_one : reesMul I F 1 = 𝟙 _ := by
  rw [reesMul, map_one, ← smulRingHom_apply, map_one]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_id _

lemma reesMul_mul (r s : reesAlgebra I) : reesMul I F (r * s) = reesMul I F s ≫ reesMul I F r := by
  rw [reesMul, reesMul, reesMul, map_mul, ← smulRingHom_apply, map_mul, ← Functor.map_comp]
  rfl

lemma reesMul_zero : reesMul I F 0 = 0 := by
  rw [reesMul, map_zero, ← smulRingHom_apply, map_zero]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_zero _ _

lemma reesMul_add (r s : reesAlgebra I) : reesMul I F (r + s) = reesMul I F r + reesMul I F s := by
  rw [reesMul, reesMul, reesMul, map_add, ← smulRingHom_apply, map_add]
  exact (Scheme.Modules.pushforward (reesPr I X)).map_add

variable {ι : Type w} (𝔘 : ι → X.Opens) (p : ℕ)

abbrev reesPre : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} := (modulesAb (reesPush I F)).obj

def reesCechRingHom : reesAlgebra I →+* AddMonoid.End (cechH (reesPre I F) 𝔘 p) where
  toFun r := cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p
  map_one' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 1)).hom p x = x
    rw [reesMul_one, modulesAbMap_id]
    exact cechHMap_id 𝔘 p x
  map_mul' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r * s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x)
    rw [reesMul_mul, modulesAbMap_comp, ← cechHMap_comp]
    rfl
  map_zero' := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F 0)).hom p x = 0
    rw [reesMul_zero]
    exact cechHMap_zero 𝔘 p x
  map_add' r s := by
    ext x
    change cechHMap 𝔘 (modulesAbMap (reesMul I F (r + s))).hom p x =
      cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x +
        cechHMap 𝔘 (modulesAbMap (reesMul I F s)).hom p x
    rw [reesMul_add, modulesAbMap_add]
    exact cechHMap_add 𝔘 _ _ p x

@[instance_reducible]
def reesCechModule : Module (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
  Module.compHom _ (reesCechRingHom I F 𝔘 p)

variable [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] {F} (hF : IsCoherent F)
  (hU : iSup 𝔘 = ⊤) (hUaff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))

omit [IsNoetherianRing A] [IsProper (X ↘ Spec (.of A))] in
include hF hU hUaff in

theorem exists_reesCech_addEquiv :
    ∃ e : cechH (reesPre I F) 𝔘 p ≃+ Sheaf.H.{u} (modulesAb (reesSheaf I F)) p,
      ∀ (r : reesAlgebra I) x, e (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) = r • e x := by
  have : (reesSheaf I F).IsQuasicoherent := (isCoherent_reesSheaf hF).1
  set pr := reesPr I X
  have hUr : ⨆ k, pr ⁻¹ᵁ 𝔘 k = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU]
    rfl
  have hUraff : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, pr ⁻¹ᵁ 𝔘 (t a)) := fun m t => by
    have h := preimage_inter pr 𝔘 t
    rw [← inter_eq_iInf (fun k => pr ⁻¹ᵁ 𝔘 k) t, ← h, inter_eq_iInf]
    exact (hUaff m t).preimage pr
  refine ⟨(cechHPushforwardEquiv pr (reesSheaf I F) 𝔘 p).trans
    (cechHAddEquivH (fun k => pr ⁻¹ᵁ 𝔘 k) hUr hUraff (reesSheaf I F) p), fun r x => ?_⟩
  simp only [AddEquiv.trans_apply]
  rw [cechHPushforwardEquiv_naturality pr (reesSheaf I F) 𝔘 p _
    (modulesAbMap (smulHom (reesSheaf I F)
      (algebraMap (reesAlgebra I) Γ(reesScheme I X, ⊤) r))).hom (fun W y => rfl) x,
    cechHAddEquivH_naturality]
  rfl

include hF hU hUaff in

theorem finite_reesCech :
    @Module.Finite (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) _ _ (reesCechModule I F 𝔘 p) := by
  let := reesCechModule I F 𝔘 p
  obtain ⟨e, he⟩ := exists_reesCech_addEquiv I 𝔘 p hF hU hUaff
  have := finite_H_of_isProper (A := reesAlgebra I) (reesSheaf I F) (isCoherent_reesSheaf hF) p
  exact Module.Finite.equiv (e.toLinearEquiv fun r x => he r x).symm

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))

omit [IsNoetherianRing A] [F.IsQuasicoherent] in
include hU in
lemma isAffineOpen_inter {m : ℕ} (t : Fin (m + 1) → ι) :
    IsAffineOpen (inter (X := X.toTopCat) 𝔘 t) := by
  rw [inter_eq_iInf]
  exact hU m t

set_option maxHeartbeats 2000000 in

lemma reesCoef_res {V V' : X.Opens} (hle : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV' n (resF _ (Scheme.Hom.preimage_mono _ hle) x) =
      resF F hle (reesCoef I hF hV n x) := by
  change (reesSectionsMap I hF hV' _).coeff n = resF F hle ((reesSectionsMap I hF hV x).coeff n)
  rw [← reesSectionsEquiv_apply, reesSectionsEquiv_res hle hF hV hV', reesSectionsEquiv_apply]
  rfl

set_option maxHeartbeats 2000000 in
lemma reesCoef_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : (reesPre I F).obj (op V)) :
    reesCoef I hF hV' n (res (reesPre I F) h x) = res (modulesAb F).obj h (reesCoef I hF hV n x) :=
  reesCoef_res I hF h hV hV' n x

set_option maxHeartbeats 2000000 in
lemma reesDeg_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesDeg I hF hV' n (res (reesPre I F) h x) =
      res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) := by
  apply idealPowι_app_injective I n
  have e1 : res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) =
    resF (idealPow I F n) h (reesDeg I hF hV n x) := rfl
  have e2 : res (reesPre I F) h x = resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) x := rfl
  rw [e1, e2, idealPowι_reesDeg, app_resF, idealPowι_reesDeg]
  exact reesCoef_res I hF h hV hV' n x

set_option maxHeartbeats 2000000 in
lemma reesInc_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(idealPow I F n, V)) :
    reesInc I hF hV' n (res (modulesAb (idealPow I F n)).obj h x) =
      res (reesPre I F) h (reesInc I hF hV n x) := by
  apply reesSectionsMap_injective hF hV'
  have e1 : res (reesPre I F) h (reesInc I hF hV n x) =
    resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) (reesInc I hF hV n x) := rfl
  have e2 : res (modulesAb (idealPow I F n)).obj h x = resF (idealPow I F n) h x := rfl
  rw [e1, e2, ← reesSectionsEquiv_apply hF hV' (resF _ _ _),
    reesSectionsEquiv_res h hF hV hV', reesSectionsEquiv_apply, reesSectionsMap_reesInc,
    reesSectionsMap_reesInc, PolynomialModule.map_lsingle, resFA_apply, app_resF]

def reesCoefFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F) (modulesAb F).obj where
  φ t := reesCoef I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesCoef_res' I hF h _ _ n x

set_option maxHeartbeats 2000000 in

def reesDegFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F)
    (modulesAb (idealPow I F n)).obj where
  φ t := reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesDeg_res' I hF h _ _ n x

set_option maxHeartbeats 2000000 in

def reesIncFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (modulesAb (idealPow I F n)).obj
    (reesPre I F) where
  φ t := reesInc I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesInc_res' I hF h _ _ n x

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) (p : ℕ)

set_option maxHeartbeats 2000000 in

lemma reesCoefFam_cechH (n : ℕ) (x : cechH (reesPre I F) 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU n).cechH p x =
      cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p ((reesDegFam I hF 𝔘 hU n).cechH p x) := by
  rw [← CechFamily.ofHom_cechH, ← CechFamily.comp_cechH]
  refine CechFamily.cechH_congr (fun t y => ?_) p x
  exact (idealPowι_reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n y).symm

set_option maxHeartbeats 2000000 in

lemma reesDegFam_reesIncFam (n : ℕ) (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesDegFam I hF 𝔘 hU n).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) = x := by
  rw [← CechFamily.comp_cechH]
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [CechFamily.cechH_cls]
  exact cls_congr 𝔘 (by funext t; exact reesDeg_reesInc I hF _ n (σ t)) _ _

set_option maxHeartbeats 2000000 in

lemma reesDegFam_reesIncFam_of_ne {n k : ℕ} (h : n ≠ k)
    (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesDegFam I hF 𝔘 hU k).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) = 0 := by
  rw [← CechFamily.comp_cechH]
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [CechFamily.cechH_cls]
  refine (cls_congr 𝔘 (by funext t; exact reesDeg_reesInc_of_ne I hF _ h (σ t)) _
    (map_zero _)).trans cls_zero

set_option maxHeartbeats 2000000 in

lemma reesCoefFam_reesIncFam (n k : ℕ) (x : cechH (modulesAb (idealPow I F n)).obj 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU k).cechH p ((reesIncFam I hF 𝔘 hU n).cechH p x) =
      if n = k then cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p x else 0 := by
  rw [reesCoefFam_cechH]
  split_ifs with h
  · subst h
    rw [reesDegFam_reesIncFam]
  · rw [reesDegFam_reesIncFam_of_ne I hF 𝔘 hU p h, map_zero]

set_option maxHeartbeats 2000000 in

lemma exists_cls_coef_eq_zero [Finite ι] (x : cechH (reesPre I F) 𝔘 p) :
    ∃ (σ : Cochain (reesPre I F) 𝔘 p) (hσ : d (reesPre I F) 𝔘 p σ = 0) (N : ℕ),
      cls σ hσ = x ∧ ∀ n, N < n → ∀ t, reesCoef I hF (isAffineOpen_inter 𝔘 hU t) n (σ t) = 0 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  refine ⟨σ, hσ, Finset.univ.sup fun t : Fin (p + 1) → ι =>
    (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id, rfl, ?_⟩
  intro n hn t
  change (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff n = 0
  by_contra h
  have h1 : n ≤ (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id :=
    Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
  have h2 := Finset.le_sup (f := fun t : Fin (p + 1) → ι =>
    (reesSectionsMap I hF (isAffineOpen_inter 𝔘 hU t) (σ t)).coeff.support.sup id)
    (Finset.mem_univ t)
  omega

set_option maxHeartbeats 2000000 in
lemma reesCoefFam_eq_zero_of_lt [Finite ι] (x : cechH (reesPre I F) 𝔘 p) :
    ∃ N : ℕ, ∀ n, N < n → (reesCoefFam I hF 𝔘 hU n).cechH p x = 0 := by
  obtain ⟨σ, hσ, N, rfl, hN⟩ := exists_cls_coef_eq_zero I hF 𝔘 hU p x
  refine ⟨N, fun n hn => ?_⟩
  rw [CechFamily.cechH_cls]
  exact (cls_congr 𝔘 (by funext t; exact hN n hn t) _ (map_zero _)).trans cls_zero

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

section Sum

variable {T : TopCat.{u}} {ι : Type u} (𝔘 : ι → Opens T) {P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {p : ℕ}

lemma cls_sum {α : Type*} (s : Finset α) (f : α → Cochain P 𝔘 p) (hf : ∀ a, d P 𝔘 p (f a) = 0)
    (h : d P 𝔘 p (∑ a ∈ s, f a) = 0) : cls (∑ a ∈ s, f a) h = ∑ a ∈ s, cls (f a) (hf a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    conv_rhs => rw [Finset.sum_empty]
    exact (cls_congr 𝔘 (Finset.sum_empty) h (map_zero _)).trans cls_zero
  | insert a s ha ih =>
    have hs : d P 𝔘 p (∑ b ∈ s, f b) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun b _ => hf b
    conv_rhs => rw [Finset.sum_insert ha, ← ih hs]
    exact (cls_congr 𝔘 (Finset.sum_insert ha) h (by rw [map_add, hf a, hs, add_zero])).trans
      (cls_add _ _ (hf a) hs _)

end Sum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)

lemma reesCoef_reesInr_smul {V : X.Opens} (hV : IsAffineOpen V) (r : reesAlgebra I) (N : ℕ)
    (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV N (reesInr I V r • s) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N, ((r : Polynomial A).coeff ij.1) • reesCoef I hF hV ij.2 s := by
  change (reesSectionsMap I hF hV (reesInr I V r • s)).coeff N = _
  rw [reesSectionsMap_smul]
  exact PolynomialModule.smul_apply (r : Polynomial A) (reesSectionsMap I hF hV s) N

variable {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) (p : ℕ)

set_option maxHeartbeats 4000000 in

lemma reesCoefFam_reesMul (r : reesAlgebra I) (N : ℕ) (x : cechH (reesPre I F) 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU N).cechH p (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
        ((r : Polynomial A).coeff ij.1) • (reesCoefFam I hF 𝔘 hU ij.2).cechH p x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  have hterm : ∀ ij : ℕ × ℕ, ((r : Polynomial A).coeff ij.1) •
      (reesCoefFam I hF 𝔘 hU ij.2).cechH p (cls σ hσ) =
      cls (push 𝔘 (smulAbRingHom F (algebraMap A Γ(X, ⊤) ((r : Polynomial A).coeff ij.1))).hom p
        ((reesCoefFam I hF 𝔘 hU ij.2).cochain p σ))
        (by rw [← push_d, ← CechFamily.cochain_d, hσ, map_zero, map_zero]) := fun ij => rfl
  rw [Finset.sum_congr rfl (fun ij _ => hterm ij), ← cls_sum]
  · rw [cechHMap_cls, CechFamily.cechH_cls]
    refine cls_congr 𝔘 (funext fun t => ?_) _ _
    rw [Finset.sum_apply]
    exact reesCoef_reesInr_smul I hF (isAffineOpen_inter 𝔘 hU t) r N (σ t)
  · rw [map_sum]
    exact Finset.sum_eq_zero fun ij _ => by
      rw [← push_d, ← CechFamily.cochain_d, hσ, map_zero, map_zero]

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open Polynomial

universe u

noncomputable section

section ReesFiltration

variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]

lemma pow_smul_le_of_smul_le {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (i j : ℕ) : I ^ i • K j ≤ K (j + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Submodule.mul_smul, ← add_assoc]
    exact (Submodule.smul_mono le_rfl ih).trans (hK _)

def reesFiltration {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1)) :
    Submodule (reesAlgebra I) (PolynomialModule A H) where
  carrier := {p | ∀ n, p.coeff n ∈ K n}
  add_mem' {p q} hp hq n := by
    have : (p + q).coeff n = p.coeff n + q.coeff n := rfl
    rw [this]
    exact add_mem (hp n) (hq n)
  zero_mem' n := by
    change (0 : PolynomialModule A H).coeff n ∈ K n
    exact (K n).zero_mem
  smul_mem' r p hp n := by
    change ((r : A[X]) • p).coeff n ∈ K n
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hr : (r : A[X]).coeff x.1 ∈ I ^ x.1 := (mem_reesAlgebra_iff I _).1 r.2 x.1
    have := pow_smul_le_of_smul_le I hK x.1 x.2 (Submodule.smul_mem_smul hr (hp x.2))
    rwa [add_comm, hx'] at this

theorem exists_eq_pow_smul_of_fg {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (hfg : (reesFiltration I hK).FG) : ∃ c, ∀ n, K (n + c) = I ^ n • K c := by
  classical
  obtain ⟨s, hs⟩ := hfg
  set c := s.sup fun p => p.coeff.support.sup id
  have hdeg : ∀ p ∈ s, ∀ j, c < j → p.coeff j = 0 := by
    intro p hp j hj
    by_contra h
    have h1 : j ≤ p.coeff.support.sup id :=
      Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
    have h2 : p.coeff.support.sup id ≤ c := Finset.le_sup (f := fun p => p.coeff.support.sup id) hp
    omega
  refine ⟨c, fun n => le_antisymm ?_ ?_⟩
  · intro x hx
    have hmem : PolynomialModule.single A (n + c) x ∈ reesFiltration I hK := by
      intro m
      rw [PolynomialModule.coeff_single, Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ hx
      · exact (K m).zero_mem
    rw [← hs, Submodule.mem_span_finset] at hmem
    obtain ⟨f, -, hf⟩ := hmem
    have hx' : x = (∑ p ∈ s, f p • p).coeff (n + c) := by
      rw [hf, PolynomialModule.coeff_single, Finsupp.single_eq_same]
    rw [hx']
    have hsum : (∑ p ∈ s, f p • p).coeff = ∑ p ∈ s, (f p • p).coeff :=
      map_sum (PolynomialModule.coeffAddEquiv (R := A) (M := H)) _ s
    rw [hsum, Finsupp.finsetSum_apply]
    refine Submodule.sum_mem _ fun p hp => ?_
    change (((f p : reesAlgebra I) : A[X]) • p).coeff (n + c) ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hy' : y.1 + y.2 = n + c := Finset.HasAntidiagonal.mem_antidiagonal.1 hy
    by_cases hj : c < y.2
    · rw [hdeg p hp y.2 hj, smul_zero]
      exact Submodule.zero_mem _
    · replace hj := not_lt.1 hj
      have hr : ((f p : reesAlgebra I) : A[X]).coeff y.1 ∈ I ^ y.1 :=
        (mem_reesAlgebra_iff I _).1 (f p).2 y.1
      have hp' : p.coeff y.2 ∈ K y.2 := by
        have : p ∈ reesFiltration I hK := hs ▸ Submodule.subset_span hp
        exact this y.2
      have hy1 : y.1 = n + (c - y.2) := by omega
      rw [hy1, pow_add] at hr
      have h1 : ((f p : reesAlgebra I) : A[X]).coeff y.1 • p.coeff y.2 ∈
          (I ^ n * I ^ (c - y.2)) • K y.2 := hy1 ▸ Submodule.smul_mem_smul hr hp'
      rw [Submodule.mul_smul] at h1
      refine Submodule.smul_mono le_rfl ?_ h1
      have := pow_smul_le_of_smul_le I hK (c - y.2) y.2
      rwa [show y.2 + (c - y.2) = c by omega] at this
  · have := pow_smul_le_of_smul_le I hK n c
    rwa [add_comm] at this

end ReesFiltration

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver reesCechModule

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) [Finite ι] (p : ℕ)

def reesBound (x : cechH (reesPre I F) 𝔘 p) : ℕ :=
  Classical.choose (reesCoefFam_eq_zero_of_lt I hF 𝔘 hU p x)

lemma reesCoefFam_eq_zero_of_bound_lt (x : cechH (reesPre I F) 𝔘 p) {n : ℕ}
    (hn : reesBound I hF 𝔘 hU p x < n) : (reesCoefFam I hF 𝔘 hU n).cechH p x = 0 :=
  Classical.choose_spec (reesCoefFam_eq_zero_of_lt I hF 𝔘 hU p x) n hn

def reesCoefPoly (x : cechH (reesPre I F) 𝔘 p) :
    PolynomialModule A (cechH (modulesAb F).obj 𝔘 p) :=
  PolynomialModule.ofCoeff A (Finsupp.onFinset (Finset.range (reesBound I hF 𝔘 hU p x + 1))
    (fun n => (reesCoefFam I hF 𝔘 hU n).cechH p x) (fun n hn => by
      rw [Finset.mem_range]
      by_contra h
      exact hn (reesCoefFam_eq_zero_of_bound_lt I hF 𝔘 hU p x (by omega))))

lemma reesCoefPoly_coeff (x : cechH (reesPre I F) 𝔘 p) (n : ℕ) :
    (reesCoefPoly I hF 𝔘 hU p x).coeff n = (reesCoefFam I hF 𝔘 hU n).cechH p x :=
  rfl

def reesΦ : cechH (reesPre I F) 𝔘 p →ₗ[reesAlgebra I]
    PolynomialModule A (cechH (modulesAb F).obj 𝔘 p) where
  toFun := reesCoefPoly I hF 𝔘 hU p
  map_add' x y := by
    apply PolynomialModule.ext
    ext n
    simp only [reesCoefPoly_coeff, PolynomialModule.coeff_add, Finsupp.add_apply, map_add]
  map_smul' r x := by
    apply PolynomialModule.ext
    ext N
    rw [reesCoefPoly_coeff, RingHom.id_apply]
    change (reesCoefFam I hF 𝔘 hU N).cechH p (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) =
      ((r : Polynomial A) • reesCoefPoly I hF 𝔘 hU p x).coeff N
    rw [reesCoefFam_reesMul, PolynomialModule.smul_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [reesCoefPoly_coeff]

lemma reesΦ_coeff (x : cechH (reesPre I F) 𝔘 p) (n : ℕ) :
    (reesΦ I hF 𝔘 hU p x).coeff n = (reesCoefFam I hF 𝔘 hU n).cechH p x :=
  reesCoefPoly_coeff I hF 𝔘 hU p x n

def cechK (n : ℕ) : Submodule A (cechH (modulesAb F).obj 𝔘 p) :=
  LinearMap.range (cechH.linearMap 𝔘 A (idealPowι I F n) p)

omit [F.IsQuasicoherent] [Finite ι] in
lemma smul_cechK_le (n : ℕ) : I • cechK I 𝔘 p (F := F) n ≤ cechK I 𝔘 p (n + 1) := by
  refine Submodule.smul_le.2 fun a ha y hy => ?_
  obtain ⟨z, rfl⟩ := hy
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  refine ⟨cechH.linearMap 𝔘 A (idealPowMul I F a ha1) p z, ?_⟩
  have h := congrArg (fun f => f.hom) (show modulesAbMap (idealPowMul I F a ha1) ≫
      modulesAbMap (idealPowι I F (n + 1)) =
      modulesAbMap (idealPowι I F n) ≫ smulAbRingHom F (algebraMap A Γ(X, ⊤) a) by
    rw [← modulesAbMap_comp, idealPowMul_ι, modulesAbMap_comp]
    rfl)
  change cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + 1))).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowMul I F a ha1)).hom p z) =
    cechHMap 𝔘 (smulAbRingHom F (algebraMap A Γ(X, ⊤) a)).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p z)
  rw [← cechHMap_comp, ← cechHMap_comp]
  exact congrArg (fun f => cechHMap 𝔘 f p z) h

lemma range_reesΦ :
    LinearMap.range (reesΦ I hF 𝔘 hU p) = reesFiltration I (smul_cechK_le I 𝔘 p (F := F)) := by
  ext P
  constructor
  · rintro ⟨x, rfl⟩ n
    change (reesΦ I hF 𝔘 hU p x).coeff n ∈ cechK I 𝔘 p n
    rw [reesΦ_coeff, reesCoefFam_cechH]
    exact ⟨_, rfl⟩
  · intro hP
    choose y hy using fun n => (hP n : P.coeff n ∈ cechK I 𝔘 p n)
    refine ⟨∑ n ∈ P.coeff.support, (reesIncFam I hF 𝔘 hU n).cechH p (y n), ?_⟩
    apply PolynomialModule.ext
    ext k
    rw [reesΦ_coeff, map_sum]
    simp_rw [reesCoefFam_reesIncFam]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · exact hy k
    · exact (Finsupp.notMem_support_iff.1 hk).symm

include hF hU in

theorem exists_cechK_eq_pow_smul [IsProper (X ↘ Spec (.of A))] (hUtop : iSup 𝔘 = ⊤) :
    ∃ c, ∀ n, cechK I 𝔘 p (F := F) (n + c) = I ^ n • cechK I 𝔘 p c := by
  refine exists_eq_pow_smul_of_fg I (smul_cechK_le I 𝔘 p) ?_
  rw [← range_reesΦ I hF 𝔘 hU p]
  have := finite_reesCech I 𝔘 p hF hUtop hU
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver reesCechModule

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules)

def transMap (n : ℕ) : (c : ℕ) → idealPow I F (n + c + 1) ⟶ idealPow I F (n + 1)
  | 0 => 𝟙 _
  | c + 1 => idealPowSucc I F (n + c + 1) ≫ transMap n c

lemma transMap_ι (n : ℕ) : ∀ c, transMap I F n c ≫ idealPowι I F (n + 1) = idealPowι I F (n + c + 1)
  | 0 => Category.id_comp _
  | c + 1 => by
    rw [transMap, Category.assoc, transMap_ι n c, idealPowSucc_ι]
    rfl

variable {F} [F.IsQuasicoherent] (hF : IsCoherent F)

lemma coeff_mem_pow_of_le (r : reesAlgebra I) {n i : ℕ} (h : n ≤ i) :
    (r : Polynomial A).coeff i ∈ I ^ n :=
  Ideal.pow_le_pow_right h ((mem_reesAlgebra_iff I _).1 r.2 i)

lemma transMap_reesDeg_smul {V : X.Opens} (hV : IsAffineOpen V) (n d : ℕ) (r : reesAlgebra I)
    (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) (hs : ∀ j, d < j → reesCoef I hF hV j s = 0) :
    (transMap I F n (d + 1)).app V (reesDeg I hF hV (n + (d + 1) + 1) (reesInr I V r • s)) =
      ∑ j : Fin (d + 1), (idealPowOfMem I F ((r : Polynomial A).coeff (n + (d + 1) + 1 - j))
        (coeff_mem_pow_of_le I r (by omega))).app V (reesCoef I hF hV j s) := by
  apply idealPowι_app_injective I (n + 1)
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, transMap_ι, idealPowι_reesDeg,
    reesCoef_reesInr_smul, map_sum]
  simp_rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, idealPowOfMem_ι]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => (r : Polynomial A).coeff l • reesCoef I hF hV k s)]
  rw [Fin.sum_univ_eq_sum_range (fun j => (smulHom F (algebraMap A Γ(X, ⊤)
    ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)))).app V (reesCoef I hF hV j s)) (d + 1)]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [hs k (by omega), map_zero]

variable {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) [Finite ι] (p : ℕ)

set_option maxHeartbeats 4000000 in
include hF hU in

theorem exists_transMap_eq_zero [IsProper (X ↘ Spec (.of A))] (hUtop : iSup 𝔘 = ⊤) :
    ∃ c, ∀ n (y : cechH (modulesAb (idealPow I F (n + c + 1))).obj 𝔘 p),
      cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom p y = 0 →
        cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom p y = 0 := by
  classical
  have := finite_reesCech I 𝔘 p hF hUtop hU
  have hnoeth : IsNoetherian (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨S, hS⟩ := hnoeth.noetherian (LinearMap.ker (reesΦ I hF 𝔘 hU p))
  choose σ hσ Nb hcls hNb using fun g => exists_cls_coef_eq_zero I hF 𝔘 hU p g
  obtain ⟨d, hd⟩ : ∃ d, d = S.sup Nb := ⟨_, rfl⟩
  refine ⟨d + 1, fun n y hy => ?_⟩
  have hκ : (reesIncFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p y ∈
      LinearMap.ker (reesΦ I hF 𝔘 hU p) := by
    rw [LinearMap.mem_ker]
    apply PolynomialModule.ext
    ext k
    rw [reesΦ_coeff, reesCoefFam_reesIncFam]
    split_ifs with h
    · subst h
      exact hy
    · rfl
  rw [← hS, Submodule.mem_span_finset] at hκ
  obtain ⟨f, -, hf⟩ := hκ
  have hy' : y = (reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (∑ g ∈ S, f g • g) := by
    rw [hf, reesDegFam_reesIncFam]
  rw [hy', map_sum, map_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hgker : reesΦ I hF 𝔘 hU p g = 0 :=
    LinearMap.mem_ker.1 (hS ▸ Submodule.subset_span hg)
  have hgd : Nb g ≤ d := hd ▸ Finset.le_sup (f := Nb) hg
  have key : ∀ r : reesAlgebra I, cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (r • g)) = 0 := by
    intro r
    rw [← hcls g]
    change cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p
        (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cls (σ g) (hσ g)))) = 0
    rw [cechHMap_cls, CechFamily.cechH_cls, cechHMap_cls]
    have hterm : ∀ j : Fin (d + 1), cechHMap 𝔘 (modulesAbMap (idealPowOfMem I F (k := n + 1)
        ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)) (coeff_mem_pow_of_le I r (by omega)))).hom p
        ((reesCoefFam I hF 𝔘 hU j).cechH p (cls (σ g) (hσ g))) = 0 := by
      intro j
      rw [hcls g, ← reesΦ_coeff, hgker, PolynomialModule.coeff_zero, Finsupp.zero_apply, map_zero]
    refine Eq.trans ?_ (Finset.sum_eq_zero (s := Finset.univ) fun j _ => hterm j)
    simp_rw [CechFamily.cechH_cls, cechHMap_cls]
    rw [← cls_sum]
    · refine cls_congr 𝔘 (funext fun t => ?_) _ _
      rw [Finset.sum_apply]
      exact transMap_reesDeg_smul I hF (isAffineOpen_inter 𝔘 hU t) n d r (σ g t)
        (fun j hj => hNb g j (by omega) t)
    · rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [← push_d, ← CechFamily.cochain_d, hσ g, map_zero, map_zero]
  exact key (f g)

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

abbrev formalα (n : ℕ) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb F) q :=
  H.linearMap A (idealPowι I F (n + 1)) q

def formalK (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb F) q) :=
  LinearMap.range (formalα I F q n)

lemma formalK_antitone : Antitone (formalK I F q) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨H.linearMap A (idealPowSucc I F (n + 1)) q x, ?_⟩
  change Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1))) q
      (Sheaf.H.map.{u} (modulesAbMap (idealPowSucc I F (n + 1))) q x) =
    Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1 + 1))) q x
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, idealPowSucc_ι]

abbrev formalβ (n : ℕ) : Sheaf.H.{u} (modulesAb F) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowπ I F n) q

abbrev formalτE (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowMap I F n) q

lemma shortExact_abSC_quotPow (n : ℕ) : (abSC (quotPowSC I F n)).ShortExact :=
  shortExact_abSC (quotPowSC_shortExact I F n)

lemma ker_formalβ (n : ℕ) : LinearMap.ker (formalβ I F q n) = formalK I F q n := by
  ext h
  constructor
  · intro hh
    exact H.exact₂ (shortExact_abSC_quotPow I F n) h hh
  · rintro ⟨x, rfl⟩
    exact H.map_g_map_f (S := abSC (quotPowSC I F n)) x

abbrev formalδ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1) :=
  H.δLinear A (shortExact_abSC_quotPow I F n) q

def formalQ (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) :=
  LinearMap.range (formalδ I F q n)

def formalι (n : ℕ) : (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  (formalK I F q n).liftQ (formalβ I F q n) (ker_formalβ I F q n).ge

lemma formalι_mk (n : ℕ) (h : Sheaf.H.{u} (modulesAb F) q) :
    formalι I F q n (Submodule.Quotient.mk h) = formalβ I F q n h := rfl

lemma formalι_injective (n : ℕ) : Function.Injective (formalι I F q n) := by
  rw [← LinearMap.ker_eq_bot, formalι, Submodule.ker_liftQ, ker_formalβ, Submodule.mkQ_map_self]

def formalπ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A] formalQ I F q n :=
  (formalδ I F q n).rangeRestrict

lemma range_formalι (n : ℕ) :
    LinearMap.range (formalι I F q n) = LinearMap.ker (formalπ I F q n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    exact H.δ_map_g (shortExact_abSC_quotPow I F n) rfl h
  · intro hy
    have hy' : formalδ I F q n y = 0 := congrArg Subtype.val hy
    obtain ⟨h, rfl⟩ := H.exact₃ (shortExact_abSC_quotPow I F n) rfl y hy'
    exact ⟨Submodule.Quotient.mk h, rfl⟩

def abSCHom {S S' : ShortComplex X.Modules} (φ : S ⟶ S') : abSC S ⟶ abSC S' where
  τ₁ := modulesAbMap φ.τ₁
  τ₂ := modulesAbMap φ.τ₂
  τ₃ := modulesAbMap φ.τ₃
  comm₁₂ := by
    change modulesAbMap φ.τ₁ ≫ modulesAbMap S'.f = modulesAbMap S.f ≫ modulesAbMap φ.τ₂
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₁₂]
  comm₂₃ := by
    change modulesAbMap φ.τ₂ ≫ modulesAbMap S'.g = modulesAbMap S.g ≫ modulesAbMap φ.τ₃
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₂₃]

def quotPowSCMap (n : ℕ) : quotPowSC I F (n + 1) ⟶ quotPowSC I F n where
  τ₁ := idealPowSucc I F (n + 1)
  τ₂ := 𝟙 F
  τ₃ := quotPowMap I F n
  comm₁₂ := by
    change idealPowSucc I F (n + 1) ≫ idealPowι I F (n + 1) = idealPowι I F (n + 2) ≫ 𝟙 F
    rw [idealPowSucc_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 F ≫ quotPowπ I F n = quotPowπ I F (n + 1) ≫ quotPowMap I F n
    rw [quotPowπ_map, Category.id_comp]

lemma formalδ_naturality (n : ℕ) (x : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q) :
    formalδ I F q n (formalτE I F q n x) =
      H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) (formalδ I F q (n + 1) x) := by
  simp only [formalδ, formalτE, H.δLinear_apply, H.linearMap_apply]
  exact H.δ_naturality (shortExact_abSC_quotPow I F (n + 1)) (shortExact_abSC_quotPow I F n)
    (abSCHom (quotPowSCMap I F n)) q (q + 1) rfl x

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

lemma formalτ_mem_formalQ (n : ℕ) (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 2))) (q + 1))
    (hy : y ∈ formalQ I F q (n + 1)) :
    H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) y ∈ formalQ I F q n := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨formalτE I F q n x, formalδ_naturality I F q n x⟩

def formalτQ (n : ℕ) : formalQ I F q (n + 1) →ₗ[A] formalQ I F q n :=
  (H.linearMap A (idealPowSucc I F (n + 1)) (q + 1)).restrict (formalτ_mem_formalQ I F q n)

abbrev formalτP : ∀ n, (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q (n + 1)) →ₗ[A]
    (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) :=
  quotTower (formalK I F q) (formalK_antitone I F q)

lemma formalι_comm (n : ℕ) :
    (formalτE I F q n).comp (formalι I F q (n + 1)) = (formalι I F q n).comp (formalτP I F q n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Sheaf.H.map.{u} (modulesAbMap (quotPowMap I F n)) q
      (Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F (n + 1))) q h) =
    Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F n)) q h
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, quotPowπ_map]

lemma formalπ_comm (n : ℕ) :
    (formalτQ I F q n).comp (formalπ I F q (n + 1)) = (formalπ I F q n).comp (formalτE I F q n) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact (formalδ_naturality I F q n x).symm

lemma surjective_formalτP (n : ℕ) : Function.Surjective (formalτP I F q n) := by
  intro x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk h, rfl⟩

variable {I F q}

theorem mem_range_formalβ_of_mem_towerLimit {c : ℕ}
    (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q} (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q))
    (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨p, hp⟩ := (bijective_towerLimitMap (formalτP I F q) (formalτE I F q) (formalτQ I F q)
    (formalι I F q) (formalπ I F q) (formalι_comm I F q) (formalπ_comm I F q)
    (formalι_injective I F q) (range_formalι I F q) hQ).2 ⟨x, hx⟩
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (p.1 n)
  refine ⟨h, ?_⟩
  have := congrArg (fun y => y.1 n) hp
  simp only at this
  rw [← this]
  change formalβ I F q n h = formalι I F q n (p.1 n)
  rw [← hh]
  rfl

theorem range_towerComp_formalτE_eq {c : ℕ} (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    (n k : ℕ) (hk : c ≤ k) :
    LinearMap.range (towerComp (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q) n k) = LinearMap.range (formalβ I F q n) := by
  rw [range_towerComp_eq_of_exact (formalτP I F q) (formalτE I F q) (formalτQ I F q)
    (formalι I F q) (formalπ I F q) (formalι_comm I F q) (formalπ_comm I F q)
    (range_formalι I F q) (surjective_formalτP I F q) hQ n k hk, formalι, Submodule.range_liftQ]

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

theorem exists_finite_affineCover (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] :
    ∃ (ι : Type u) (_ : Finite ι) (𝔘 : ι → X.Opens), iSup 𝔘 = ⊤ ∧
      ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => (V : Set X))
    (fun V => V.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  refine ⟨s, inferInstance, fun V => V.1.1, ?_, fun m t => IsAffineOpen.iInf fun a => (t a).1.2⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

lemma isSeparated_of_over [IsSeparated (X ↘ Spec (.of A))] : X.IsSeparated := by
  refine ⟨?_⟩
  rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

lemma cechK_succ_le {ι : Type u} (𝔘 : ι → X.Opens) (p n : ℕ) :
    cechK I 𝔘 p (F := F) (n + 1) ≤ cechK I 𝔘 p n := by
  rintro _ ⟨z, rfl⟩
  refine ⟨cechH.linearMap 𝔘 A (idealPowSucc I F n) p z, ?_⟩
  have h := congrArg (fun f => f.hom) (show modulesAbMap (idealPowSucc I F n) ≫
      modulesAbMap (idealPowι I F n) = modulesAbMap (idealPowι I F (n + 1)) by
    rw [← modulesAbMap_comp, idealPowSucc_ι])
  change cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowSucc I F n)).hom p z) =
    cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + 1))).hom p z
  rw [← cechHMap_comp]
  exact congrArg (fun f => cechHMap 𝔘 f p z) h

lemma towerComp_formalτQ_val (q n : ℕ) : ∀ (c : ℕ) (y : formalQ I F q (n + c)),
    ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c y : formalQ I F q n) :
      Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (transMap I F n c) (q + 1) y
  | 0, y => by
    change (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (𝟙 _) (q + 1) y
    rw [H.linearMap_id]
    rfl
  | c + 1, y => by
    change ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c
      (formalτQ I F q (n + c) y) : formalQ I F q n) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) = _
    rw [towerComp_formalτQ_val q n c, transMap, H.linearMap_comp]
    rfl

variable [IsProper (X ↘ Spec (.of A))] (hF : IsCoherent F)

include hF in
lemma exists_formalK_le (q : ℕ) : ∃ c, ∀ n, formalK I F q (n + c) ≤
    I ^ n • (⊤ : Submodule A (Sheaf.H.{u} (modulesAb F) q)) := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_cechK_eq_pow_smul I hF 𝔘 hU q hUtop
  refine ⟨c, fun n => ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨zČ, rfl⟩ := (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) q).surjective z
  rw [formalα, ← cechHLinearEquivH_naturality]
  have h2 := cechK_succ_le I 𝔘 q (n + c) (F := F) ⟨zČ, rfl⟩
  rw [hc n] at h2
  have hmem : cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) q zČ ∈
      I ^ n • (⊤ : Submodule A (cechH (modulesAb F).obj 𝔘 q)) :=
    Submodule.smul_mono le_rfl le_top h2
  refine Submodule.smul_induction_on hmem (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha trivial
  · rw [map_add]
    exact add_mem hy hy'

include hF in
lemma exists_towerComp_formalτQ_eq_zero (q : ℕ) :
    ∃ c, ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0 := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_transMap_eq_zero I hF 𝔘 hU (q + 1) hUtop
  refine ⟨c, fun n => LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [towerComp_formalτQ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  obtain ⟨x, hx⟩ := y.2
  obtain ⟨yČ, hyČ⟩ :=
    (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) (q + 1)).surjective y.1
  have hι : cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom (q + 1) yČ = 0 := by
    apply (cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)).injective
    rw [map_zero]
    change cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)
      (cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) (q + 1) yČ) = 0
    rw [cechHLinearEquivH_naturality, hyČ, ← hx]
    exact H.map_f_δ (shortExact_abSC_quotPow I F (n + c)) rfl x
  rw [← hyČ, ← cechHLinearEquivH_naturality]
  change cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + 1)) (q + 1)
    (cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom (q + 1) yČ) = 0
  rw [hc n yČ hι, map_zero]

include hF in

theorem formalFunctions_mem_range (q : ℕ) {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q}
    (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q)
      (formalτE I F q)) (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨c, hc⟩ := exists_towerComp_formalτQ_eq_zero I hF q
  exact mem_range_formalβ_of_mem_towerLimit hc hx n

end

end GroundTheory.Arith.SchemeCoh
end
