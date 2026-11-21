import Mathlib
import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateInfinite.DescentMaps
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSeq
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransportGS
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SPicFinite
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersFinite
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.UnitsDefs
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

noncomputable section

section Sha

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

def shaSubmodule (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) : Submodule k (cohomology A n) where
  carrier := {x | ∀ v, (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom x = 0}
  add_mem' {x y} hx hy v := by
    change (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom (x + y) = 0
    rw [map_add, hx v, hy v, add_zero]
  zero_mem' v := map_zero _
  smul_mem' c x hx v := by
    change (cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) n).hom (c • x) = 0
    rw [map_smul, hx v, smul_zero]

theorem cohomologyMap_mem_shaSubmodule {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (f : A ⟶ B)
    {n : ℕ} {x : cohomology A n} (hx : x ∈ shaSubmodule φ A n) :
    (cohomologyMap f n).hom x ∈ shaSubmodule φ B n := by
  intro v
  have e1 := cohomologyMapAlong_comp_apply_of_eq (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (MonoidHom.id G) continuous_id (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (fun _ => rfl)
    f (𝟙 _) ((Rep.resFunctor (φ v).toMonoidHom).map f) (fun _ => rfl) n x
  rw [cohomologyMapAlong_id_eq_cohomologyMap] at e1
  have e2 := cohomologyMap_cohomologyMapAlong_apply (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (𝟙 _) ((Rep.resFunctor (φ v).toMonoidHom).map f) n x
  rw [Category.id_comp] at e2
  rw [e1, ← e2, hx v, map_zero]

theorem mem_ptSha_iff_mem_shaSubmodule (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] {n : ℕ}
    (x : cohomology A n) : x ∈ ptSha φ A n ↔ x ∈ shaSubmodule φ A n := by
  refine ⟨fun hx v => ptRes_eq_zero_of_mem_ptSha φ A hx v, fun hx => ?_⟩
  rw [mem_ptSha]
  funext v
  exact hx v

end Sha

section Nsmul

theorem bijective_nsmul_of_dvd {A : Type*} [AddCommGroup A] {m n : ℕ} (hmn : m ∣ n)
    (hn : Function.Bijective fun a : A => n • a) : Function.Bijective fun a : A => m • a := by
  obtain ⟨c, rfl⟩ := hmn
  refine ⟨fun a b hab => hn.1 ?_, fun a => ?_⟩
  · have hab' : m • a = m • b := hab
    change (m * c) • a = (m * c) • b
    rw [mul_comm, ← smul_smul, ← smul_smul, hab']
  · obtain ⟨b, rfl⟩ := hn.2 a
    exact ⟨c • b, by change m • c • b = (m * c) • b; rw [smul_smul]⟩

end Nsmul

section Instances

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

instance isDiscreteRep_res_subtype_res_toMonoidHom {H' : Type u} [Group H'] [TopologicalSpace H']
    (ψ : H' →ₜ* G) (B : Rep.{u} k G) [IsDiscreteRep B] (S : Subgroup H') :
    IsDiscreteRep (Rep.res S.subtype (Rep.res ψ.toMonoidHom B)) :=
  haveI := IsDiscreteRep.res (continuous_toMonoidHom ψ) B
  IsDiscreteRep.res (continuous_subgroup_subtype S) _

instance isDiscreteRep_res_toMonoidHom_res_subtype {H' : Type u} [Group H'] [TopologicalSpace H']
    (S : Subgroup G) (ψ : H' →ₜ* S) (B : Rep.{u} k G) [IsDiscreteRep B] :
    IsDiscreteRep (Rep.res ψ.toMonoidHom (Rep.res S.subtype B)) :=
  haveI := IsDiscreteRep.res (continuous_subgroup_subtype S) B
  IsDiscreteRep.res (continuous_toMonoidHom ψ) _

end Instances

section Descent

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (V : OpenSubgroup G) (A : Rep.{u} k G) [IsDiscreteRep A]

def mackeyTranslateMor (p : MackeyIndex V φ) :
    Rep.res (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype
        (Rep.res (φ p.1).toMonoidHom A) ⟶
      Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) :=
  Rep.ofHom ⟨A.ρ p.2.out, fun h => by
    ext a
    change A.ρ p.2.out (A.ρ ((φ p.1) (h : Hv p.1)) a) =
      A.ρ (p.2.out * (φ p.1) (h : Hv p.1) * p.2.out⁻¹) (A.ρ p.2.out a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

def mackeyTranslateInv (p : MackeyIndex V φ) :
    Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) ⟶
      Rep.res (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out).subtype
        (Rep.res (φ p.1).toMonoidHom A) :=
  Rep.ofHom ⟨A.ρ p.2.out⁻¹, fun h => by
    ext a
    change A.ρ p.2.out⁻¹ (A.ρ (p.2.out * (φ p.1) (h : Hv p.1) * p.2.out⁻¹) a) =
      A.ρ ((φ p.1) (h : Hv p.1)) (A.ρ p.2.out⁻¹ a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩

omit [CompactSpace G] [∀ v, CompactSpace (Hv v)] in
theorem cohomologyMap_mackeyTranslateMor_injective (p : MackeyIndex V φ) (n : ℕ) :
    Function.Injective (cohomologyMap (mackeyTranslateMor φ V A p) n).hom := by
  have h : mackeyTranslateMor φ V A p ≫ mackeyTranslateInv φ V A p = 𝟙 _ := by
    ext a
    change A.ρ p.2.out⁻¹ (A.ρ p.2.out a) = a
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine Function.LeftInverse.injective (g := (cohomologyMap (mackeyTranslateInv φ V A p) n).hom) fun z => ?_
  rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h, cohomologyMap_id]
  rfl

omit [∀ v, CompactSpace (Hv v)] in

theorem cohomologyMapAlong_mackeyFamily_cohomologyRes (p : MackeyIndex V φ) (n : ℕ) (y : cohomology A n) :
    (cohomologyMapAlong (mackeyFamily V φ p).toMonoidHom (continuous_toMonoidHom (mackeyFamily V φ p)) (𝟙 _) n).hom
        ((cohomologyRes A (V : Subgroup G) n).hom y) =
      (cohomologyMap (mackeyTranslateMor φ V A p) n).hom
        ((cohomologyRes (Rep.res (φ p.1).toMonoidHom A)
          (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) n).hom
          ((cohomologyMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) (𝟙 _) n).hom y)) := by
  set x := p.2.out

  let φ' : mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x →* G :=
    (φ p.1).toMonoidHom.comp (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype
  have hφ' : Continuous φ' :=
    (continuous_toMonoidHom (φ p.1)).comp (continuous_subgroup_subtype _)
  let g' : Rep.res φ' A ⟶ Rep.res (mackeyFamily V φ p).toMonoidHom (Rep.res (V : Subgroup G).subtype A) :=
    Rep.ofHom ⟨A.ρ x, fun h => by
      ext a
      change A.ρ x (A.ρ ((φ p.1) (h : Hv p.1)) a) = A.ρ (x * (φ p.1) (h : Hv p.1) * x⁻¹) (A.ρ x a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩

  let c : (V : Subgroup G) →* G := (innerConjHom x).comp (V : Subgroup G).subtype
  have hc : Continuous c := (continuous_innerConjHom x).comp (continuous_subgroup_subtype _)
  let g₁ : Rep.res c A ⟶ Rep.res (V : Subgroup G).subtype A :=
    Rep.ofHom ⟨A.ρ x, fun h => by
      ext a
      change A.ρ x (A.ρ (x⁻¹ * (h : G) * x) a) = A.ρ (h : G) (A.ρ x a)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩
  have s1 : (cohomologyRes A (V : Subgroup G) n).hom y =
      (cohomologyMapAlong c hc g₁ n).hom y := by
    conv_lhs => rw [← cohomologyInnerConj_apply A n x y]
    exact cohomologyMapAlong_comp_apply_of_eq (V : Subgroup G).subtype (continuous_subgroup_subtype _)
      (innerConjHom x) (continuous_innerConjHom x) c hc (fun _ => rfl) (innerConjMor A x) (𝟙 _) g₁
      (fun _ => rfl) n y
  have s2 := cohomologyMapAlong_comp_apply_of_eq (mackeyFamily V φ p).toMonoidHom
    (continuous_toMonoidHom (mackeyFamily V φ p)) c hc φ' hφ' (fun h => by
      change x⁻¹ * (x * (φ p.1) (h : Hv p.1) * x⁻¹) * x = (φ p.1) (h : Hv p.1)
      group) g₁ (𝟙 _) g' (fun _ => rfl) n y

  have s3 := cohomologyMap_cohomologyMapAlong_apply
    (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype (continuous_subgroup_subtype _)
    (𝟙 _) (mackeyTranslateMor φ V A p) n
    ((cohomologyMapAlong (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) (𝟙 _) n).hom y)
  have s4 := cohomologyMapAlong_comp_apply_of_eq
    (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom x).subtype (continuous_subgroup_subtype _)
    (φ p.1).toMonoidHom (continuous_toMonoidHom (φ p.1)) φ' hφ' (fun _ => rfl) (𝟙 _)
    (𝟙 _ ≫ mackeyTranslateMor φ V A p) g' (fun _ => rfl) n y
  rw [s1, s2, cohomologyRes_eq, s3, s4]

variable [(V : Subgroup G).Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem index_mackeySubgroup_dvd {H : Type u} [Group H] (ψ : H →* G) (x : G) :
    (mackeySubgroup (V : Subgroup G) ψ x).index ∣ (V : Subgroup G).index := by
  rw [mackeySubgroup, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem mem_shaSubmodule_iff_cohomologyRes (hA : Function.Bijective fun a : A => (V : Subgroup G).index • a)
    (n : ℕ) (y : cohomology A n) :
    y ∈ shaSubmodule φ A n ↔
      (cohomologyRes A (V : Subgroup G) n).hom y ∈
        shaSubmodule (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n := by
  constructor
  · intro hy p
    rw [cohomologyMapAlong_mackeyFamily_cohomologyRes, hy p.1, map_zero, map_zero]
  · intro hy v
    let p : MackeyIndex V φ := ⟨v, DoubleCoset.mk (V : Subgroup G) (φ v).toMonoidHom.range 1⟩
    have h0 := hy p
    rw [cohomologyMapAlong_mackeyFamily_cohomologyRes] at h0
    have h1 := cohomologyMap_mackeyTranslateMor_injective φ V A p n (h0.trans (map_zero _).symm)
    have hB : Function.Bijective fun a : Rep.res (φ p.1).toMonoidHom A =>
        ((mackeyOpenSubgroup V (continuous_toMonoidHom (φ p.1)) p.2.out : OpenSubgroup (Hv p.1)) :
          Subgroup (Hv p.1)).index • a :=
      bijective_nsmul_of_dvd (index_mackeySubgroup_dvd V (φ p.1).toMonoidHom p.2.out) hA
    exact cohomologyRes_injective_of_bijective (mackeyOpenSubgroup V (continuous_toMonoidHom (φ p.1)) p.2.out)
      (Rep.res (φ p.1).toMonoidHom A) hB n (h1.trans (map_zero _).symm)

end Descent

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Representation

universe u

noncomputable section

section Coordinates

variable {k H N : Type*} [CommRing k] [AddCommGroup H] [Module k H] [AddCommGroup N] [Module k N]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι k N)

def coordTensor (i : ι) : TensorProduct k H N →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H (b.coord i)

omit [Fintype ι] in
theorem coordTensor_tmul (i : ι) (y : H) (m : N) : coordTensor b i (y ⊗ₜ[k] m) = b.coord i m • y := by
  simp [coordTensor]

theorem sum_coordTensor_tmul (z : TensorProduct k H N) : ∑ i, coordTensor b i z ⊗ₜ[k] b i = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | tmul y m =>
    calc ∑ i, coordTensor b i (y ⊗ₜ[k] m) ⊗ₜ[k] b i = ∑ i, y ⊗ₜ[k] (b.repr m i • b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coordTensor_tmul, TensorProduct.smul_tmul, Module.Basis.coord_apply]
      _ = y ⊗ₜ[k] m := by rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add z w hz hw =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [Finset.sum_add_distrib, hz, hw]

omit [Fintype ι] in

theorem coordTensor_rTensor {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H) (i : ι)
    (w : TensorProduct k X N) : coordTensor b i (f.rTensor N w) = f (coordTensor b i w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rw [LinearMap.rTensor_tmul, coordTensor_tmul, coordTensor_tmul, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem mem_range_rTensor_iff {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H)
    (z : TensorProduct k H N) :
    z ∈ LinearMap.range (f.rTensor N) ↔ ∀ i, coordTensor b i z ∈ LinearMap.range f := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨coordTensor b i w, (coordTensor_rTensor b f i w).symm⟩
  · intro h
    choose w hw using h
    refine ⟨∑ i, w i ⊗ₜ[k] b i, ?_⟩
    rw [map_sum]
    simp_rw [LinearMap.rTensor_tmul, hw]
    exact sum_coordTensor_tmul b z

end Coordinates

section Twist

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)]
  (Q : Subgroup G) (ψ : ∀ v, Hv v →ₜ* Q) (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hM : ∀ (g : Q) (m : M), M.ρ g m = m) {ιb : Type*} [Fintype ιb] (b : Module.Basis ιb k M)

def resTensorFormMor (f : M →ₗ[k] k) : Rep.res Q.subtype (T ⊗ M) ⟶ Rep.res Q.subtype T :=
  (resTensorIso Q.subtype T M).hom ≫
    tensorFormMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) f
      (form_invariant_of_forall_eq (M := Rep.res Q.subtype M) hM f)

theorem cohomologyMap_resTensorFormMor_twistResMap (f : M →ₗ[k] k) (n : ℕ)
    (y : cohomology (Rep.res Q.subtype T) n) (m : M) :
    (cohomologyMap (resTensorFormMor Q T M hM f) n).hom (twistResMap Q T M hM n (y ⊗ₜ[k] m)) = f m • y := by
  rw [twistResMap_tmul, ← ModuleCat.comp_apply, ← cohomologyMap_comp]
  have e : (tensorRightMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) m (fun h => hM h m) ≫
      (resTensorIso Q.subtype T M).inv) ≫ resTensorFormMor Q T M hM f = f m • 𝟙 _ := by
    ext t
    change f m • t = f m • t
    rfl
  rw [e, cohomologyMap_smul, cohomologyMap_id]
  rfl

omit [Fintype ιb] in

theorem cohomologyMap_resTensorFormMor_coord_twistResMap (n : ℕ) (i : ιb)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    (cohomologyMap (resTensorFormMor Q T M hM (b.coord i)) n).hom (twistResMap Q T M hM n z) =
      coordTensor b i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y m => rw [cohomologyMap_resTensorFormMor_twistResMap, coordTensor_tmul]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]

theorem twistResMap_mem_shaSubmodule_iff (n : ℕ)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    twistResMap Q T M hM n z ∈ shaSubmodule ψ (Rep.res Q.subtype (T ⊗ M)) n ↔
      ∀ i, coordTensor b i z ∈ shaSubmodule ψ (Rep.res Q.subtype T) n := by
  constructor
  · intro h i
    rw [← cohomologyMap_resTensorFormMor_coord_twistResMap Q T M hM b n i z]
    exact cohomologyMap_mem_shaSubmodule ψ _ h
  · intro h
    rw [← sum_coordTensor_tmul b z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twistResMap_tmul]
    exact cohomologyMap_mem_shaSubmodule ψ _ (h i)

end Twist

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)
  [Module.Finite k M] (hTr : Module.finrank k T = 1) (hP : ((P : Subgroup G).index : k) ≠ 0)

theorem coe_coprimeTwistEquiv (n : ℕ) (x : cohomology M n) :
    haveI := isDiscreteRep_homRep P T M hT hM
    haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
    haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
    twistResEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n
        (coprimeTwistEquiv P T M hT hM hTr hP n x) =
      (cohomologyRes (T ⊗ homRep T M) (P : Subgroup G) n).hom
        ((cohomologyMap (evalInv T M hTr) n).hom x) := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  rw [← twistInvariantsEquiv_apply]
  simp only [coprimeTwistEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem mem_shaSubmodule_iff_coprimeTwistEquiv {ιb : Type*} [Fintype ιb]
    (b : Module.Basis ιb k (homRep T M)) (n : ℕ) (x : cohomology M n) :
    x ∈ shaSubmodule φ M n ↔
      ∀ i, coordTensor b i (coprimeTwistEquiv P T M hT hM hTr hP n x : TensorProduct k
        (cohomology (Rep.res (P : Subgroup G).subtype T) n) (homRep T M)) ∈
          shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))

  have h1 : x ∈ shaSubmodule φ M n ↔
      (cohomologyMap (evalInv T M hTr) n).hom x ∈ shaSubmodule φ (T ⊗ homRep T M) n := by
    refine ⟨cohomologyMap_mem_shaSubmodule φ _, fun h => ?_⟩
    have e : (cohomologyMap (evalMor T M) n).hom ((cohomologyMap (evalInv T M hTr) n).hom x) = x := by
      rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, evalInv_comp_evalMor, cohomologyMap_id]
      rfl
    rw [← e]
    exact cohomologyMap_mem_shaSubmodule φ _ h
  rw [h1, mem_shaSubmodule_iff_cohomologyRes φ P _ (bijective_nsmul_of_ne_zero hP), ← coe_coprimeTwistEquiv P T M hT hM hTr hP n x,
    twistResEquiv_apply]
  exact twistResMap_mem_shaSubmodule_iff (P : Subgroup G) (mackeyFamily P φ) T (homRep T M)
    (homRep_ρ_of_mem P T M hT hM) b n _

include hTr hP in

theorem finrank_shaSubmodule_eq_finrank_invariants (n : ℕ) {X : Type u} [AddCommGroup X] [Module k X]
    (ρX : Representation k (G ⧸ (P : Subgroup G)) X)
    (e : X →ₗ[k] cohomology (Rep.res (P : Subgroup G).subtype T) n)
    (he : ρX.IsIntertwiningMap (cohomologyConjRep T (P : Subgroup G) n) e) (hinj : Function.Injective e)
    (hrange : ∀ y, y ∈ shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n ↔
      y ∈ LinearMap.range e) :
    Module.finrank k (shaSubmodule φ M n) = Module.finrank k
      (ρX.tprod (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants := by
  classical
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  set σ := quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM)
  set E := coprimeTwistEquiv P T M hT hM hTr hP n
  set R := e.rTensor (homRep T M)
  have hR : (ρX.tprod σ).IsIntertwiningMap ((cohomologyConjRep T (P : Subgroup G) n).tprod σ) R :=
    isIntertwiningMap_rTensor σ he
  have hRinj : Function.Injective R := Module.Flat.rTensor_preserves_injective_linearMap e hinj
  let Ψ : (ρX.tprod σ).invariants →ₗ[k] ((cohomologyConjRep T (P : Subgroup G) n).tprod σ).invariants :=
    R.restrict (mapsTo_invariants hR)
  let Φ : (ρX.tprod σ).invariants →ₗ[k] cohomology M n := E.symm.toLinearMap ∘ₗ Ψ
  have hΦinj : Function.Injective Φ := fun w w' h =>
    Subtype.ext (hRinj (congrArg Subtype.val (E.symm.injective h)))
  let b := Module.Free.chooseBasis k (homRep T M)
  have hrangeΦ : LinearMap.range Φ = shaSubmodule φ M n := by
    ext x
    rw [mem_shaSubmodule_iff_coprimeTwistEquiv φ P T M hT hM hTr hP b n x]
    constructor
    · rintro ⟨w, rfl⟩ i
      have hEw : (E (Φ w) : TensorProduct k (cohomology (Rep.res (P : Subgroup G).subtype T) n)
          (homRep T M)) = R w := by
        change ((E (E.symm (Ψ w)) : _)) = R w
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [hEw, coordTensor_rTensor]
      exact (hrange _).2 ⟨_, rfl⟩
    · intro h
      obtain ⟨w₀, hw₀⟩ := (mem_range_rTensor_iff b e _).2 fun i => (hrange _).1 (h i)
      have hinv : w₀ ∈ (ρX.tprod σ).invariants := fun q => hRinj (by
        rw [hR.isIntertwining, hw₀]
        exact (E x).2 q)
      refine ⟨⟨w₀, hinv⟩, ?_⟩
      change E.symm (Ψ ⟨w₀, hinv⟩) = x
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hw₀
  rw [← hrangeΦ, LinearMap.finrank_range_of_inj hΦinj]

end Descent

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ℓ : ℕ) [NeZero ℓ] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

def gsRootsLocalUnitsMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S ℓ) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  gsRootsOmegaMor S ιs ℓ v ≫
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f

theorem gsRootsLocalUnitsMor_eq (v : S) :
    gsRootsLocalUnitsMor S ιs ℓ v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) ≫ gsSUnitsLocalMor S ιs v :=
  (gsKummerLocalMap S ιs ℓ v).comm₁₂.symm

include hℓS in

theorem cohomologyMap_gsRootsLocalUnitsMor_injective (v : S) :
    Function.Injective (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom := by
  have h2 := cohomologyMap_f_injective_of_subsingleton (localKummer_shortExact S ℓ v) 1
    subsingleton_cohomology_one_galUnits
  have h1 : Function.Injective (cohomologyMap (gsRootsOmegaMor S ιs ℓ v) 2).hom := by
    have hc := congrArg (fun φ => cohomologyMap φ 2)
      (comp_repInvOfBijective (gsRootsOmegaMor S ιs ℓ v) (bijective_gsRootsOmegaMor S ιs ℓ hℓS v))
    have hc' := (cohomologyMap_comp _ _ 2).symm.trans (hc.trans (cohomologyMap_id 2))
    refine Function.LeftInverse.injective (g := (cohomologyMap (repInvOfBijective
      (gsRootsOmegaMor S ιs ℓ v) (bijective_gsRootsOmegaMor S ιs ℓ hℓS v)) 2).hom) fun a => ?_
    exact congrArg (fun φ => φ.hom a) hc'
  have e := cohomologyMap_comp (gsRootsOmegaMor S ιs ℓ v)
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f 2
  intro a b hab
  have hab' := (congrArg (fun φ => φ.hom a) e).symm.trans ((hab : _).trans (congrArg (fun φ => φ.hom b) e))
  exact h1 (h2 hab')

include hℓS in

theorem ptRes_eq_zero_iff (v : S) (x : cohomology (gsRoots S ℓ) 2) :
    ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x = 0 ↔
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 := by
  have e1 := cohomologyMap_cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (𝟙 _) (gsRootsLocalUnitsMor S ιs ℓ v) (p := 2) x
  have e2 := cohomologyMapAlong_cohomologyMap (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)
    (gsSUnitsLocalMor S ιs v) (p := 2) x
  have e3 := congrArg (fun m => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) m 2).hom x)
    ((Category.id_comp (gsRootsLocalUnitsMor S ιs ℓ v)).trans (gsRootsLocalUnitsMor_eq S ιs ℓ v))
  have key : (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom
      (ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) :=
    e1.trans (e3.trans e2.symm)
  constructor
  · intro h
    exact key.symm.trans ((congrArg (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom h).trans
      (map_zero _))
  · intro h
    exact cohomologyMap_gsRootsLocalUnitsMor_injective S ιs ℓ hℓS v ((key.trans h).trans (map_zero _).symm)

variable {ℓ} (hℓ : ℓ.Prime)

set_option maxHeartbeats 4000000 in
omit [NeZero ℓ] in
include hℓS hℓ in

theorem eq_zero_of_gsSUnitsLocalMor_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : ℓ • y = 0)
    (hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsSUnitsLocalMor S ιs v) 2).hom y = 0) : y = 0 := by
  classical
  have hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hy1 : ℓ ^ 1 • y = 0 := by rw [pow_one]; exact hy
  refine eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS y 1 hy1 ?_
  refine eq_zero_of_brauerLocal_apply_eq_zero (gsLocalEmbeddings S ιs) _ fun w => ?_
  rcases w with w | w
  · apply placeInv_injective (K := K) (.inl w)
    refine (placeInv_inl_eq_zero (ℓ ^ 1) (hK.imp (fun h => h.pow) id) w _ ?_).trans (map_zero _).symm
    have e : ℓ ^ 1 • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) = 0 := by
      rw [← map_nsmul, ← map_nsmul, hy1, map_zero, map_zero]
    exact (map_nsmul (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
      (Sum.inl w : Place K.1)) (ℓ ^ 1) _).symm.trans
      ((congrArg (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
        (Sum.inl w : Place K.1)) e).trans (map_zero _))
  · by_cases hw : w ∈ S
    · refine (congrArg (fun z => brauerLocal (gsLocalEmbeddings S ιs) z (.inr w))
        (sUnitsBrauer_apply K S _)).trans ?_
      refine (brauerLocal_gsBrauerInfl_inr K S (gsLocalEmbeddings S ιs) w _).trans ?_
      have hfin : (gsLocalEmbeddings S ιs).fin w = ιs ⟨w, hw⟩ := gsLocalEmbeddings_fin S ιs ⟨w, hw⟩
      rw [hfin]
      refine (gsLocalRes_sUnitsToUnits_eq S ιs ⟨w, hw⟩ _).trans ?_
      rw [hloc ⟨w, hw⟩, map_zero, map_zero]
      rfl
    · exact brauerLocal_sUnitsBrauer_inr K S _ _ w hw

include hℓS hℓ in

theorem mem_ptSha_iff_cohomologyMap_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (x : cohomology (gsRoots S ℓ) 2) :
    x ∈ ptSha (gsFinFamily S ιs) (gsRoots S ℓ) 2 ↔
      (cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x = 0 := by
  rw [mem_ptSha]
  constructor
  · intro hx
    have hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      fun v => (ptRes_eq_zero_iff S ιs ℓ hℓS v x).1 (congrFun hx v)
    have h0 : (cohomologyMap (ℓ • 𝟙 (galSUnitsMax K.1 ℚ̄ S)) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      cohomologyMap_g_cohomologyMap_f_apply
        (S := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2 x
    exact eq_zero_of_gsSUnitsLocalMor_eq_zero S ιs hℓS hℓ hK _
      ((cohomologyMap_nsmul_id_apply (galSUnitsMax K.1 ℚ̄ S) ℓ 2 _).symm.trans h0) hloc
  · intro hy
    funext v
    exact (ptRes_eq_zero_iff S ιs ℓ hℓS v x).2 ((congrArg _ hy).trans (map_zero _))

include hℓS hℓ in

theorem mem_ptSha_iff_exists_δ (hK : Odd ℓ ∨ IsTotallyComplex K.1) (x : cohomology (gsRoots S ℓ) 2) :
    x ∈ ptSha (gsFinFamily S ιs) (gsRoots S ℓ) 2 ↔
      ∃ z : cohomology (galSUnitsMax K.1 ℚ̄ S) 1,
        (δ (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl).hom z = x := by
  refine (mem_ptSha_iff_cohomologyMap_eq_zero S ιs hℓS hℓ hK x).trans ⟨fun h => ?_, ?_⟩
  · exact exists_δ_eq_of_cohomologyMap_f_eq_zero (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl x h
  · rintro ⟨z, rfl⟩
    exact congrArg (fun φ => φ.hom z) (δ_comp (sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ hℓS) 1 2 rfl)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))}
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 800000 in

theorem ptCompactToGlobal_gsMackeyCompactIso (ℓ : ℕ)
    (c : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c) =
      (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom
        ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
          (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c) := by
  have hT := compactTransport_compactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
    (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
    (gsRootsOfUnityIso S hL ℓ).symm.hom 2
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hC : (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom =
      compactTransport (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
        (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
        (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    gsMackeyCompactIso_hom hL ιs _ 2
  have s1 := congrArg (fun ψ => (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom (ψ.hom c)) hC
  have s3 := congrArg (fun ψ => ψ.hom ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c)) hG
  have s2 := congrArg (fun φ => φ.hom c) hT
  exact s1.trans (s2.trans s3.symm)

set_option maxHeartbeats 800000 in

theorem mem_ptSha_mackey_iff (ℓ : ℕ)
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x ∈
        ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
          (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_ptCompactToGlobal_eq_of_mem_ptSha
      (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) hx
    obtain ⟨c', hc'⟩ := (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).toLinearEquiv.surjective c
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').symm.trans
      ((congrArg (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL)
        (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom hc').trans hc)
    have h2 := (gsRootsOfUnityCohomologyIso S hL ℓ 2).toLinearEquiv.injective h1
    exact (congrArg (· ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) h2).mp
      (ptCompactToGlobal_mem_ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) c')
  · intro hx
    have hc := exists_ptCompactToGlobal_eq_of_mem_ptSha _ _ hx
    obtain ⟨c', hc'⟩ := hc
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').trans
      (congrArg (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom hc')
    exact (congrArg (· ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) h1).mp
      (ptCompactToGlobal_mem_ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ))
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c'))

theorem gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits (ℓ : ℕ) [NeZero ℓ] :
    (gsRootsOfUnityIso S hL ℓ).symm.hom ≫ (Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) =
      (Rep.resFunctor (gsBaseChange S hL).toMulEquiv.toMonoidHom).map
        (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) ≫
        (gsSUnitsIso S hL).symm.hom :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

set_option maxHeartbeats 800000 in

theorem cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso (ℓ : ℕ) [NeZero ℓ]
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom
        ((gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x) =
      (gsSUnitsCohomologyIso S hL 2).hom.hom
        ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
          (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x) := by
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hO : (gsSUnitsCohomologyIso S hL 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsSUnitsIso S hL).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have s1 := congrArg (fun ψ => (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
    (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom (ψ.hom x)) hG
  have s4 := congrArg (fun ψ => ψ.hom ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
    (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x)) hO
  have s2 := cohomologyMap_cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom
    ((Rep.resFunctor (gsSubtype S hL)).map (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ))
    (p := 2) x
  have s3 := cohomologyMapAlong_cohomologyMap (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL))
    (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ)
    (gsSUnitsIso S hL).symm.hom (p := 2) x
  have s5 := congrArg (fun m => (cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) m 2).hom x)
    (gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits hL ℓ)
  exact s1.trans (s2.trans (s5.trans (s3.symm.trans s4.symm)))

theorem gsRootsOfUnityCohomologyIso_hom_inv_apply (ℓ : ℕ)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x) = x :=
  congrArg (fun φ => φ.hom x) (gsRootsOfUnityCohomologyIso S hL ℓ 2).inv_hom_id

set_option maxHeartbeats 800000 in

theorem mem_ptSha_mackey_iff_of_eq (ℓ : ℕ)
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x' ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  subst hx
  exact mem_ptSha_mackey_iff hL ιs ℓ x'

set_option maxHeartbeats 800000 in

theorem cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq (ℓ : ℕ) [NeZero ℓ]
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    (cohomologyMap (rootsOfUnityToSUnits (placesOver S)
      (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x' = 0 ↔
      (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom x = 0 := by
  subst hx
  rw [cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso hL ℓ x']
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact (gsSUnitsCohomologyIso S hL 2).toLinearEquiv.injective (h0.trans (map_zero _).symm)

set_option maxHeartbeats 1600000 in

theorem mem_ptSha_mackey_iff_exists_kummerModN {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      ∃ y, kummerModNHom (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsKummer_shortExact S ℓ hℓS) 1 y = x := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hℓS' : ∀ w ∉ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))), ((ℓ : ℕ) : 𝓞 L.1) ∉ w.asIdeal :=
    natCast_not_mem_of_not_mem_placesOver hn
  have hx' := gsRootsOfUnityCohomologyIso_hom_inv_apply hL ℓ x
  refine (mem_ptSha_mackey_iff_of_eq hL ιs ℓ hx').trans
    ((mem_ptSha_iff_cohomologyMap_eq_zero (K := L) (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
      (gsMackeyEmbeddings hL ιs) hℓS' hℓ hK ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x)).trans
    ((cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq hL ℓ hx').trans
    (Iff.trans ?_ (kummerTorsHom_eq_zero_iff (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsKummer_shortExact S ℓ hℓS) 1 x))))
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory IntermediateField

universe u

noncomputable section

section Restrict

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [Normal F L]

instance instNormalGsOpenSubgroup :
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)).Normal :=
  gsOpenSubgroup_normal hL

theorem ker_gsRestrictGal_le :
    (gsRestrictGal (S := S) hL).ker ≤ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) :=
  (ker_gsRestrictGal hL).le

end Restrict

section Units

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem map_gsEmbedding_mem_sUnitsMax {x : Lˣ}
    (hx : x ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
    Units.map (gsEmbedding hL : L →* maxUnramifiedOutside F Ω S) x ∈ sUnitsMax F Ω S := by
  have hx' := (mem_sUnitsOf_iff_mem_unit (F := F) (L := L) S).2 hx
  refine ⟨?_, ?_⟩
  · exact hx'.1.map ((gsEmbedding hL).restrictScalars (S.integer F))
  · rw [← map_inv]
    exact hx'.2.map ((gsEmbedding hL).restrictScalars (S.integer F))

def sUnitsToGsInvariants :
    Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) →+
      (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)).ρ.invariants where
  toFun x := ⟨Additive.ofMul ⟨Units.map (gsEmbedding hL : L →* maxUnramifiedOutside F Ω S)
      (x.toMul : Lˣ), map_gsEmbedding_mem_sUnitsMax hL x.toMul.2⟩, fun p => by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact (mem_gsOpenSubgroup_iff S hL (p : galUnramifiedOutside F Ω S)).1 p.2 _⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Subtype.ext (map_one _)))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Subtype.ext (map_mul _ _ _)))

theorem coe_sUnitsToGsInvariants_apply
    (x : Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    (((Additive.toMul ((sUnitsToGsInvariants hL x : _) : Additive (sUnitsMax F Ω S)) :
      sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) =
        gsEmbedding hL (((Additive.toMul x : (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :
          Lˣ) : L) :=
  rfl

theorem sUnitsToGsInvariants_injective : Function.Injective (sUnitsToGsInvariants hL) := by
  intro x y hxy
  have h := congrArg (fun z : (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)).ρ.invariants =>
    (((Additive.toMul (z : Additive (sUnitsMax F Ω S)) : sUnitsMax F Ω S) :
      (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S)) hxy
  simp only [coe_sUnitsToGsInvariants_apply] at h
  exact Additive.toMul.injective (Subtype.ext (Units.ext ((gsEmbedding hL).injective h)))

theorem exists_gsEmbedding_eq_of_forall {y : maxUnramifiedOutside F Ω S}
    (hy : ∀ p ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)), p y = y) :
    ∃ x : L, gsEmbedding hL x = y := by
  have hmem : y ∈ IntermediateField.fixedField
      (IntermediateField.fixingSubgroup (gsEmbedding (S := S) hL).fieldRange) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun p hp => hy p hp
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

theorem sUnitsToGsInvariants_surjective : Function.Surjective (sUnitsToGsInvariants hL) := by
  rintro ⟨a, ha⟩
  set u : sUnitsMax F Ω S := Additive.toMul a
  have hfix : ∀ p ∈ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)),
      p ((u : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) =
        ((u : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) := fun p hp =>
    congrArg (fun z : Additive (sUnitsMax F Ω S) =>
      ((((Additive.toMul z : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ)) :
        maxUnramifiedOutside F Ω S)) (ha ⟨p, hp⟩)
  obtain ⟨x, hx⟩ := exists_gsEmbedding_eq_of_forall hL hfix
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact (u : (maxUnramifiedOutside F Ω S)ˣ).ne_zero hx.symm
  have hxinv : gsEmbedding hL x⁻¹ =
      (((u⁻¹ : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) : maxUnramifiedOutside F Ω S) := by
    rw [map_inv₀, hx, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  have hint : ∀ {z : L}, IsIntegral (S.integer F) (gsEmbedding hL z) → IsIntegral (S.integer F) z :=
    fun h => (isIntegral_algHom_iff ((gsEmbedding hL).restrictScalars (S.integer F))
      (gsEmbedding (S := S) hL).injective).1 h
  have hmem : Units.mk0 x hx0 ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
    refine (mem_sUnitsOf_iff_mem_unit (F := F) (L := L) S).1 ⟨?_, ?_⟩
    · refine hint ?_
      rw [Units.val_mk0, hx]
      exact u.2.1
    · refine hint ?_
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, hxinv]
      exact (u⁻¹).2.1
  refine ⟨Additive.ofMul ⟨Units.mk0 x hx0, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact hx

def gsH0SUnitsEquiv :
    cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0 ≃+
      Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) :=
  (H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).toLinearEquiv.toAddEquiv.trans
    (AddEquiv.ofBijective (sUnitsToGsInvariants hL)
      ⟨sUnitsToGsInvariants_injective hL, sUnitsToGsInvariants_surjective hL⟩).symm

theorem gsEmbedding_gsH0SUnitsEquiv
    (x : cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0) :
    gsEmbedding hL (((Additive.toMul (gsH0SUnitsEquiv hL x) :
        (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) : Lˣ) : L) =
      (((Additive.toMul ((H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).hom.hom x :
        Additive (sUnitsMax F Ω S)) : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) :
          maxUnramifiedOutside F Ω S) := by
  rw [← coe_sUnitsToGsInvariants_apply]
  have e : sUnitsToGsInvariants hL (gsH0SUnitsEquiv hL x) =
      (H0Iso (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S))).hom.hom x :=
    AddEquiv.apply_symm_apply (AddEquiv.ofBijective (sUnitsToGsInvariants hL)
      ⟨sUnitsToGsInvariants_injective hL, sUnitsToGsInvariants_surjective hL⟩) _
  rw [e]

variable [Normal F L]

theorem gsH0SUnitsEquiv_cohomologyConj (g : galUnramifiedOutside F Ω S)
    (x : cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0) :
    gsH0SUnitsEquiv hL ((cohomologyConj (galSUnitsMax F Ω S)
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) 0 g).hom x) =
      GroundTheory.Global.sUnitRep (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
        (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw) (gsRestrictGal hL g) (gsH0SUnitsEquiv hL x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  refine (gsEmbedding (S := S) hL).injective ?_
  show gsEmbedding hL _ = gsEmbedding hL _
  rw [gsEmbedding_gsH0SUnitsEquiv, H0Iso_hom_cohomologyConj, GroundTheory.Global.sUnitRep_apply]
  change _ = gsEmbedding hL ((((GroundTheory.Global.sUnitMap (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
    (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw) (gsRestrictGal hL g)
    (Additive.toMul (gsH0SUnitsEquiv hL x))) :
      (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L) : Lˣ) : L)
  rw [GroundTheory.Global.coe_sUnitMap, gsEmbedding_gsRestrictGal, gsEmbedding_gsH0SUnitsEquiv]
  rfl

theorem conj_gsH0SUnits_eq {l : ℕ} (d : AdditiveFunction.{u} l (L ≃ₐ[F] L))
    [Finite (ModN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) l)]
    [Finite (TorsN (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L)) l)] :
    (letI := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
        (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL)
        (galSUnitsMax F Ω S) 0;
      d.g (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0)) =
    (letI := sUnitAction (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
        (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw);
      d.g (Additive ((placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L))) := by
  let := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S))
    (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL) (galSUnitsMax F Ω S) 0
  let := sUnitAction (K := F) (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
    (fun τ _ hw => galSmul_mem_placesOver (S := S) τ hw)
  have : Finite (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 0 ⧸
      (gsH0SUnitsEquiv hL).symm.toAddMonoidHom.range) := by
    rw [AddMonoidHom.range_eq_top.2 (gsH0SUnitsEquiv hL).symm.surjective]
    infer_instance
  refine d.g_eq_of_finite_cokernel (gsH0SUnitsEquiv hL).symm.toAddMonoidHom (fun γ b => ?_)
    (gsH0SUnitsEquiv hL).symm.injective
  obtain ⟨g, rfl⟩ := gsRestrictGal_surjective hL γ
  apply (gsH0SUnitsEquiv hL).injective
  change gsH0SUnitsEquiv hL ((gsH0SUnitsEquiv hL).symm _) =
    gsH0SUnitsEquiv hL (gsRestrictGal hL g • (gsH0SUnitsEquiv hL).symm b)
  rw [conjActionOf_smul, gsH0SUnitsEquiv_cohomologyConj, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  rfl

end Units

section H1

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)

theorem finite_gsH1SUnits :
    Finite (cohomology (Rep.res (gsSubtype S hL) (galSUnitsMax F Ω S)) 1) := by
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  have : Finite (cohomology (galSUnitsMax L Ω (placesOver S : Set (HeightOneSpectrum (𝓞 L)))) 1) :=
    Finite.of_injective _ (h1SUnitsToSPic_injective (F := L) (Ω := Ω)
      (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
  exact Finite.of_equiv _ (gsSUnitsCohomologyIso S hL 1).toLinearEquiv.toEquiv

end H1

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global Representation

local notation "ℚ̄" => AlgebraicClosure ℚ

universe u

noncomputable section

section Scalars

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A] [IsDiscreteRep A'] (e : A ≃+ A')
  (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

theorem mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv e he n x ∈ shaSubmodule φ A' n ↔ x ∈ shaSubmodule φ A n := by
  refine forall_congr' fun v => ?_
  have key := cohomologyAddEquivOfEquiv_mapAlong e he (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
    (B := Rep.res (φ v).toMonoidHom A) (B' := Rep.res (φ v).toMonoidHom A') e (fun _ a => he _ a) (𝟙 _) (𝟙 _)
    (fun _ => rfl) n x
  rw [← key]
  constructor
  · intro h
    exact (cohomologyAddEquivOfEquiv (A := Rep.res (φ v).toMonoidHom A) (A' := Rep.res (φ v).toMonoidHom A')
      e (fun _ a => he _ a) n).injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

end Scalars

section Card

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (ℓ : ℕ) [Fact ℓ.Prime]
  (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (hM : ∀ m : M, ℓ • m = 0)


end Card

section KummerZMod

attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  {T O : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep T] [IsDiscreteRep O] {ℓ : ℕ} {f : T ⟶ O}
  {w : f ≫ (ℓ • 𝟙 O) = 0} (hS : (ShortComplex.mk f (ℓ • 𝟙 O) w).ShortExact) (hT : ∀ t : T, ℓ • t = 0)

def kummerModNZMod (i : ℕ) :
    ModN (cohomology (Rep.res N.subtype O) i) ℓ →ₗ[ZMod ℓ]
      cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) :=
  ((cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).toAddMonoidHom.comp
      (kummerModNHom N hS i)).toZModLinearMap ℓ

theorem kummerModNZMod_apply (i : ℕ) (y : ModN (cohomology (Rep.res N.subtype O) i) ℓ) :
    kummerModNZMod N hS hT i y =
      cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1) (kummerModNHom N hS i y) :=
  rfl

theorem kummerModNZMod_injective (i : ℕ) : Function.Injective (kummerModNZMod N hS hT i) :=
  (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T) (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT))
    (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)).injective.comp (kummerModNHom_injective N hS i)

variable [N.Normal] [CompactSpace N]

theorem isIntertwiningMap_kummerModNZMod (i : ℕ) :
    (letI := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i;
      modNRep (G ⧸ N) (cohomology (Rep.res N.subtype O) i) ℓ).IsIntertwiningMap
      (cohomologyConjRep (zmodRepOfTorsion ℓ T hT) N (i + 1)) (kummerModNZMod N hS hT i) := by
  let _ := conjActionOf N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i
  refine ⟨fun q x => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      have hs : (g : G ⧸ N) • y = (cohomologyConj O N i g).hom y :=
        conjActionOf_smul N (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N).le O i g y
      rw [modNRep_mk, hs, cohomologyConjRep_mk, kummerModNZMod_apply, kummerModNZMod_apply,
        kummerModNHom_cohomologyConj]
      exact cohomologyAddEquivOfEquiv_cohomologyConj (A := T) (A' := zmodRepOfTorsion ℓ T hT)
        (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) N (i + 1) g _

omit [N.Normal] [CompactSpace N] in

theorem mem_shaSubmodule_iff_mem_range_kummerModNZMod {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)]
    [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] (ψ : ∀ v, Hv v →ₜ* N) (i : ℕ)
    (hsha : ∀ x : cohomology (Rep.res N.subtype T) (i + 1),
      x ∈ ptSha ψ (Rep.res N.subtype T) (i + 1) ↔ ∃ y, kummerModNHom N hS i y = x)
    (y : cohomology (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1)) :
    y ∈ shaSubmodule ψ (Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (i + 1) ↔
      y ∈ LinearMap.range (kummerModNZMod N hS hT i) := by
  set E := cohomologyAddEquivOfEquiv (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl) (i + 1)
  obtain ⟨y', rfl⟩ := E.surjective y
  refine (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff ψ (A := Rep.res N.subtype T)
    (A' := Rep.res N.subtype (zmodRepOfTorsion ℓ T hT)) (zmodRepOfTorsionEquiv ℓ T hT) (fun _ _ => rfl)
    (i + 1) y').trans ?_
  refine (mem_ptSha_iff_mem_shaSubmodule ψ _ y').symm.trans ((hsha y').trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [kummerModNZMod_apply, hz]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, E.injective (by rw [← hz, kummerModNZMod_apply])⟩

end KummerZMod

section GS

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ℓ : ℕ) [Fact ℓ.Prime]

abbrev gsRootsZMod : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S) :=
  zmodRepOfTorsion ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)

theorem finrank_gsRootsZMod {S} (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨f⟩ := nonempty_addEquiv_gsRoots_of_mem S (n := ℓ) fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hcard : Nat.card (gsRootsZMod S ℓ) = ℓ ^ 1 := by
    rw [pow_one]
    exact (Nat.card_congr f.toEquiv).trans (Nat.card_zmod ℓ)
  have : Finite (gsRootsZMod S ℓ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  exact finrank_eq_of_natCard_zmod ℓ hcard

variable {S} (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [(gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]

abbrev gsH1SUnitsModRep :
    Representation (ZMod ℓ)
      (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
      (ModN (cohomology (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
        (galSUnitsMax K.1 ℚ̄ S)) 1) ℓ) :=
  letI := conjActionOf (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le (galSUnitsMax K.1 ℚ̄ S) 1
  modNRep _ _ ℓ

theorem finrank_shaSubmodule_two_eq_finrank_invariants (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hT : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (t : gsRootsZMod S ℓ),
      (gsRootsZMod S ℓ).ρ g t = t)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M hT hM))).invariants := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hP : (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 hcop.symm
  exact finrank_shaSubmodule_eq_finrank_invariants (gsFinFamily S ιs) (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M
    hT hM (finrank_gsRootsZMod ℓ hℓS) hP 2 (gsH1SUnitsModRep ℓ hL)
    (kummerModNZMod _ (gsKummer_shortExact S ℓ hℓS) (nsmul_galRootsOfUnity_eq_zero ℓ) 1)
    (isIntertwiningMap_kummerModNZMod _ (gsKummer_shortExact S ℓ hℓS) (nsmul_galRootsOfUnity_eq_zero ℓ) 1)
    (kummerModNZMod_injective _ (gsKummer_shortExact S ℓ hℓS) (nsmul_galRootsOfUnity_eq_zero ℓ) 1)
    (mem_shaSubmodule_iff_mem_range_kummerModNZMod _ (gsKummer_shortExact S ℓ hℓS) (nsmul_galRootsOfUnity_eq_zero ℓ)
      (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) 1
      (mem_ptSha_mackey_iff_exists_kummerModN hL ιs hℓ hℓS hK))


end GS

end

end GroundTheory.ProfCoh
end
