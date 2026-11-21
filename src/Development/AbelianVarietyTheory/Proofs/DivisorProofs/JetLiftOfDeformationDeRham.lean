import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_group_morphism_base_change : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC := by
  first | exact @GlobalTheory.LatJet.isBC_jetRing | exact GlobalTheory.LatJet.isBC_jetRing | (intros; apply GlobalTheory.LatJet.isBC_jetRing <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_lift_along_split_surjection : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.abelianScheme_constLift | exact GlobalTheory.abelianScheme_constLift | (intros; apply GlobalTheory.abelianScheme_constLift <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open TensorProduct

namespace GlobalTheory.LatJet.JetFil

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
  {J : JetRing R I n} {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}

theorem crys_ext (hm : m.IsBC) {d₁ d₂ : Crys J.κ (spMap J.π) X.A} (h : ∀ c, d₁ (m.pull c) = d₂ (m.pull c)) :
    d₁ = d₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

theorem bcMap_apply (hm : m.IsBC) (h : HdR X.A) (c : primDR X.A) :
    hm.bcMap h (m.pull c) = algebraMap R J.B (h c) :=
  (hm.corr_iff.2 rfl : m.Corr h (hm.bcMap h)) c

theorem red_pull (c : primDR X.A) : (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).pull (m.pull c) = c :=
  (GrpMor.pull_pull m (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (fun r ↦ J.π_algebraMap r) (by simp) c).trans (Subtype.ext (IsMor.pullCohomologyOne_id _ c.1))

theorem jet_filtration_proj_section_eq_zero (i : I) : J.π (J.t i) = 0 := by
  rw [J.π_eq, JetRing.t, J.b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  have := congrFun (congrArg Subtype.val h) i
  simp at this

theorem finite_idx : Finite (Idx I n) :=
  Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (ν.1 j)) (Finset.mem_univ i)).trans ν.2)⟩ : Fin (n + 2)))
    fun a b h ↦ Subtype.ext (funext fun i ↦ by simpa using congrFun h i)

noncomputable def fintypeIdx : Fintype (Idx I n) := @Fintype.ofFinite _ finite_idx

attribute [local instance] fintypeIdx

def co (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) : HdR X.A where
  toFun c := J.b.repr (d (m.pull c)) ν
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' r c := by
    rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

theorem co_apply (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) (c : primDR X.A) :
    co hm ν d c = J.b.repr (d (m.pull c)) ν := rfl

theorem co_add (hm : m.IsBC) (ν : Idx I n) (d₁ d₂ : Crys J.κ (spMap J.π) X.A) :
    co hm ν (d₁ + d₂) = co hm ν d₁ + co hm ν d₂ :=
  LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.add_apply, map_add, Finsupp.add_apply]

theorem co_zero (hm : m.IsBC) (ν : Idx I n) : co hm ν (0 : Crys J.κ (spMap J.π) X.A) = 0 :=
  LinearMap.ext fun c ↦ by simp only [co_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]

theorem co_smul_bc (hm : m.IsBC) (ν : Idx I n) (β : J.B) (h : HdR X.A) :
    co hm ν (β • hm.bcMap h) = J.b.repr β ν • h :=
  LinearMap.ext fun c ↦ by
    rw [co_apply, LinearMap.smul_apply, bcMap_apply, smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def,
      map_smul, Finsupp.smul_apply, smul_eq_mul, LinearMap.smul_apply, smul_eq_mul, mul_comm]

theorem eq_sum_co (hm : m.IsBC) (d : Crys J.κ (spMap J.π) X.A) :
    d = ∑ ν, J.b ν • hm.bcMap (co hm ν d) := by
  refine crys_ext hm fun c ↦ ?_
  rw [LinearMap.sum_apply]
  conv_lhs => rw [← J.b.sum_repr (d (m.pull c))]
  refine Finset.sum_congr rfl fun ν _ ↦ ?_
  rw [LinearMap.smul_apply, bcMap_apply, co_apply, smul_eq_mul, Algebra.smul_def, mul_comm]

def bcE (hm : m.IsBC) : J.B ⊗[R] HdR X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A := liftSemi hm.bcMap

theorem bcE_bijective (hm : m.IsBC) : Function.Bijective (bcE hm) := by
  let G : Crys J.κ (spMap J.π) X.A → J.B ⊗[R] HdR X.A := fun d ↦ ∑ ν, J.b ν ⊗ₜ co hm ν d
  have hG : ∀ z, G (bcE hm z) = z := fun z ↦ by
    induction z with
    | zero => simp only [G, map_zero, co_zero, tmul_zero, Finset.sum_const_zero]
    | add x y hx hy =>
      simp only [G, map_add, co_add, tmul_add, Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy]
    | tmul β h =>
      simp only [G, bcE, liftSemi_tmul, co_smul_bc, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
      rw [J.b.sum_repr]
  refine ⟨Function.LeftInverse.injective hG, fun d ↦ ⟨∑ ν, J.b ν ⊗ₜ co hm ν d, ?_⟩⟩
  simp only [map_sum, bcE, liftSemi_tmul]
  exact (eq_sum_co hm d).symm

section Tensor

variable {A M : Type*} [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]

theorem isCompl_span_tmul {p q : Submodule R M} (h : IsCompl p q) :
    IsCompl (Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (p : Set M)))
      (Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (q : Set M))) := by
  let P := (q.projection p h.symm).baseChange A
  have hp : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (p : Set M)), P z = 0 := fun z hz ↦ by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_right h.symm hy, tmul_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have hq : ∀ z ∈ Submodule.span A ((fun x ↦ (1 : A) ⊗ₜ[R] x) '' (q : Set M)), P z = z := fun z hz ↦ by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [LinearMap.baseChange_tmul, Submodule.projection_apply_of_mem_left h.symm hy]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  refine ⟨Submodule.disjoint_def.2 fun z h₁ h₂ ↦ (hq z h₂).symm.trans (hp z h₁), codisjoint_iff.2 ?_⟩
  refine (Submodule.eq_top_iff'.2 fun z ↦ ?_)
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul β x =>
    obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top : x ∈ p ⊔ q)
    have e : ∀ w : M, β ⊗ₜ[R] w = β • ((1 : A) ⊗ₜ[R] w) := fun w ↦ by rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [tmul_add, e, e]
    exact add_mem (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)))
  | add x y hx hy => exact add_mem hx hy

end Tensor

variable {N : I → Module.End R (HdR X.A)}

def nilK (N : I → Module.End R (HdR X.A)) : Module.End J.B (J.B ⊗[R] HdR X.A) :=
  ∑ i, J.t i • (N i).baseChange J.B

theorem nilK_sq (hN : ∀ i j, N i * N j = 0) : nilK (J := J) N * nilK N = 0 := by
  have h : ∀ i j, (N i).baseChange J.B * (N j).baseChange J.B = 0 := fun i j ↦ by
    rw [Module.End.mul_eq_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, hN,
      LinearMap.baseChange_zero]
  simp only [nilK, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, h, smul_zero, Finset.sum_const_zero]

def jetAut (hN : ∀ i j, N i * N j = 0) : (J.B ⊗[R] HdR X.A) ≃ₗ[J.B] (J.B ⊗[R] HdR X.A) :=
  LinearEquiv.ofLinear (1 + nilK N) (1 - nilK N)
    (by
      rw [← Module.End.mul_eq_comp, ← Module.End.one_eq_id]
      have : (1 + nilK (J := J) N) * (1 - nilK N) = 1 - nilK N * nilK N := by noncomm_ring
      rw [this, nilK_sq hN, sub_zero])
    (by
      rw [← Module.End.mul_eq_comp, ← Module.End.one_eq_id]
      have : (1 - nilK (J := J) N) * (1 + nilK N) = 1 - nilK N * nilK N := by noncomm_ring
      rw [this, nilK_sq hN, sub_zero])

def jetEquiv (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) :
    (J.B ⊗[R] HdR X.A) ≃ₗ[J.B] Crys J.κ (spMap J.π) X.A :=
  (jetAut hN).trans (LinearEquiv.ofBijective (bcE hm) (bcE_bijective hm))

theorem jetEquiv_tmul (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) :
    jetEquiv hm hN (1 ⊗ₜ x) = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := by
  simp only [jetEquiv, jetAut, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply, LinearEquiv.ofBijective_apply,
    LinearMap.add_apply, Module.End.one_apply, nilK, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.baseChange_tmul, map_add, map_sum, map_smul, bcE, liftSemi_tmul, one_smul]

theorem jetEquiv_tmul_apply (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) (c : primDR X.A) :
    jetEquiv hm hN (1 ⊗ₜ x) (m.pull c) = algebraMap R J.B (x c) + ∑ i, J.t i * algebraMap R J.B (N i x c) := by
  rw [jetEquiv_tmul, LinearMap.add_apply, LinearMap.sum_apply, bcMap_apply]
  simp only [LinearMap.smul_apply, bcMap_apply, smul_eq_mul]

theorem isJetElt_iff (hm : m.IsBC) (hN : ∀ i j, N i * N j = 0) (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) :
    IsJetElt J X N m x d ↔ d = jetEquiv hm hN (1 ⊗ₜ x) :=
  ⟨fun h ↦ crys_ext hm fun c ↦ (h c).trans (jetEquiv_tmul_apply hm hN x c).symm,
    fun h c ↦ h ▸ jetEquiv_tmul_apply hm hN x c⟩

theorem corr_iff (hm : m.IsBC) (d : Crys J.κ (spMap J.π) X.A) (y : HdR X.A) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y ↔ ∀ c, y c = J.π (d (m.pull c)) := by
  constructor
  · intro H c
    have := H (m.pull c)
    rwa [red_pull] at this
  · intro H c'
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | zero => simp
    | add x z hx hz => simp only [map_add, hx, hz]
    | tmul β c =>
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ, red_pull, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, H c]

theorem exists_red_mem (hm : m.IsBC) {d : Crys J.κ (spMap J.π) X.A}
    (hd : d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) :
    ∃ y ∈ Fil X.A, ∀ c, y c = J.π (d (m.pull c)) := by
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, hj⟩ := hd
    refine ⟨x, hx, fun c ↦ ?_⟩
    rw [hj c, map_add, map_sum]
    simp [jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]
  | zero => exact ⟨0, zero_mem _, fun c ↦ by simp⟩
  | add d₁ d₂ _ _ h₁ h₂ =>
    obtain ⟨y₁, hy₁, e₁⟩ := h₁
    obtain ⟨y₂, hy₂, e₂⟩ := h₂
    exact ⟨y₁ + y₂, add_mem hy₁ hy₂, fun c ↦ by simp [e₁, e₂]⟩
  | smul β d _ h =>
    obtain ⟨y₁, hy₁, e₁⟩ := h
    exact ⟨J.π β • y₁, Submodule.smul_mem _ _ hy₁, fun c ↦ by simp [e₁]⟩

theorem fil_compl (HR : GlobalTheory.Published.AbelianDeRham) (X : Obj F 𝔠 (Sp R)) : ∃ C, IsCompl (Fil X.A) C :=
  ((GlobalTheory.Published.GrothendieckMessing.canonical_of_abelianDeRham (κ := dividedPowersBot R) (π := RingHom.id R) HR
    (isDPNilpotent_bot R) Function.surjective_id ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)) _
    X.A X.A _ ((GlobalTheory.CrysConn.isGrpPullback_refl X.A).congr (Cris.spMap_id R).symm rfl) X.ab X.dim).2.1

end GlobalTheory.LatJet.JetFil

namespace GlobalTheory.LatJet

open GlobalTheory.LatJet.JetFil

theorem jetFil_summand_reduces : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      (∃ N' : Submodule J.B (Crys J.κ (spMap J.π) X.A), IsCompl (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) N') ∧
      ∀ y : HdR X.A, y ∈ Fil X.A ↔ ∃ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y := by
  intro HG HR HD F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m
  have hm := isBC_jetRing HG HR HD F 𝔠 R I n J X m
  have hN' : ∀ i j, N i * N j = 0 := hN.2.1
  obtain ⟨C, hC⟩ := fil_compl HR X
  have hS : {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} =
      jetEquiv hm hN' '' ((fun x ↦ (1 : J.B) ⊗ₜ[R] x) '' (Fil X.A : Set (HdR X.A))) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, isJetElt_iff hm hN', SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  refine ⟨?_, fun y ↦ ⟨fun hy ↦ ?_, ?_⟩⟩
  · rw [hS]
    have h := (Submodule.orderIsoMapComap (jetEquiv hm hN')).isCompl (isCompl_span_tmul (A := J.B) hC)
    simp only [Submodule.orderIsoMapComap_apply, Submodule.map_span] at h
    exact ⟨_, h⟩
  · refine ⟨jetEquiv hm hN' (1 ⊗ₜ y), Submodule.subset_span ⟨y, hy, (isJetElt_iff hm hN' y _).2 rfl⟩,
      (corr_iff hm _ _).2 fun c ↦ ?_⟩
    rw [jetEquiv_tmul_apply, map_add, map_sum]
    simp [jet_filtration_proj_section_eq_zero, JetRing.π_algebraMap]
  · rintro ⟨d, hd, hc⟩
    obtain ⟨y', hy', e⟩ := exists_red_mem hm hd
    have : y = y' := LinearMap.ext fun c ↦ ((corr_iff hm d y).1 hc c).trans (e c).symm
    exact this ▸ hy'

end GlobalTheory.LatJet
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_group_morphism_de_rham_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      (∃ N' : Submodule J.B (Crys J.κ (spMap J.π) X.A), IsCompl (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) N') ∧
      ∀ y : HdR X.A, y ∈ Fil X.A ↔ ∃ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y := by
  atlas_forward_decl GlobalTheory.LatJet.jetFil_summand_reduces
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.JetStable

set_option autoImplicit false

theorem isJetElt_act {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)) (hN : ∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)))
    (a : 𝓞 F) (x : HdR X.A) (d : Crys J.κ (spMap J.π) X.A) (hd : IsJetElt J X N m x d) :
    IsJetElt J X N m (act (dp0 R) (𝟙 _) X.rm a x) (act J.κ (spMap J.π) X.rm a d) := by
  haveI := X.rm.hom a
  intro c
  have k := (homMor (dp0 R) (𝟙 _) (X.rm.act a)).comp m
  have e1 : primPull J.κ (spMap J.π) (X.rm.act a) (m.pull c) = k.pull c :=
    GrpMor.pull_pull m (homMor J.κ (spMap J.π) (X.rm.act a)) k (fun _ ↦ rfl) (by simp) c
  have e2 : m.pull (primPull (dp0 R) (𝟙 _) (X.rm.act a) c) = k.pull c :=
    GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (X.rm.act a)) m k (fun _ ↦ rfl) rfl c
  have hc : ∀ i, N i (act (dp0 R) (𝟙 _) X.rm a x) = act (dp0 R) (𝟙 _) X.rm a (N i x) := fun i ↦
    LinearMap.congr_fun (hN i a).eq x
  rw [act_apply, push_apply, e1, ← e2, hd]
  simp only [hc]
  rfl

theorem act_mem_Fil {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (a : 𝓞 F) {x : HdR X.A} (hx : x ∈ Fil X.A) :
    act (dp0 R) (𝟙 _) X.rm a x ∈ Fil X.A := by
  haveI := X.rm.hom a
  rw [act_apply]
  exact push_mem_Fil _ hx

end GlobalTheory.LatJet.JetStable

open GlobalTheory.LatJet.JetStable in

theorem GlobalTheory.LatJet.jetFil_act_stable : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (a : 𝓞 F), ∀ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, act J.κ (spMap J.π) X.rm a d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  intro _ _ _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m a
  have key : Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} ≤
      (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}).comap (act J.κ (spMap J.π) X.rm a) := by
    refine Submodule.span_le.2 fun d ⟨x, hx, hd⟩ ↦ Submodule.subset_span ?_
    exact ⟨_, act_mem_Fil X a hx, isJetElt_act J X N hN.1 m a x d hd⟩
  exact fun d hd ↦ key hd
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_morphism_compatible_nilpotent : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (a : 𝓞 F), ∀ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, act J.κ (spMap J.π) X.rm a d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  atlas_forward_decl GlobalTheory.LatJet.jetFil_act_stable
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_morphism_uniqueness : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (c : 𝔠.elt) (φ : Crys J.κ (spMap J.π) X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A →ₗ[J.B] J.B),
        GlobalTheory.AbDual.IsCorrForm J.κ (spMap J.π) X.A X.A (X.P c) φ → ∀ a ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, ∀ b ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, φ a b = 0 := by
  first | exact @GlobalTheory.JetIsotropic.jetFil_isotropic | exact GlobalTheory.JetIsotropic.jetFil_isotropic | (intros; apply GlobalTheory.JetIsotropic.jetFil_isotropic <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_object_lift_divided_powers : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → ∀ (hI : RingHom.ker π = I)
    (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left), IsGrpPullback X₀.A A (spMap π) i →
    IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
    ∀ (E : Submodule R (Crys κ (spMap π) X₀.A)), (∃ N : Submodule R (Crys κ (spMap π) X₀.A), IsCompl E N) →
      (∀ y : HdR X₀.A, y ∈ Fil X₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI X₀.A).Corr d y) →
      (∀ (a : 𝓞 F), ∀ d ∈ E, act κ (spMap π) X₀.rm a d ∈ E) →
      (∀ (c : 𝔠.elt) (φ : Crys κ (spMap π) X₀.A →ₗ[R] Crys κ (spMap π) X₀.A →ₗ[R] R),
        GlobalTheory.AbDual.IsCorrForm κ (spMap π) X₀.A X₀.A (X₀.P c) φ → ∀ a ∈ E, ∀ b ∈ E, φ a b = 0) →
      ∃ (X' : Obj F 𝔠 (Sp R)) (i' : X₀.A.left ⟶ X'.A.left) (pull : X₀.IsPullBy X' (spMap π) i'), liftFil κ pull.grp = E := by
  first | exact @GlobalTheory.RMDeform.exists_deform | exact GlobalTheory.RMDeform.exists_deform | (intros; apply GlobalTheory.RMDeform.exists_deform <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetLiftMain

theorem exists_jetLift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    ∃ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  intro hGD hDR hDC F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m
  have hs : J.π.comp (algebraMap R J.B) = RingHom.id R := RingHom.ext fun r ↦ JetRing.π_algebraMap J r
  obtain ⟨A, _, i, h, hA, hg⟩ := GlobalTheory.T.abelian_scheme_lift_along_split_surjection J.B R J.π (algebraMap R J.B) hs X.A _ X.ab X.dim
  obtain ⟨hsum, hred⟩ := GlobalTheory.T.jet_ring_group_morphism_de_rham_lift hGD hDR hDC F 𝔠 R I n J X N hN m
  exact GlobalTheory.T.group_object_lift_divided_powers hGD hDR hDC F 𝔠 J.B R (RingHom.ker J.π) J.κ J.nil J.π
    (fun r ↦ ⟨algebraMap R J.B r, JetRing.π_algebraMap J r⟩) rfl X A i h hA hg _ hsum hred
    (GlobalTheory.T.jet_ring_morphism_compatible_nilpotent hGD hDR hDC F 𝔠 R I n J X N hN m) (GlobalTheory.T.jet_ring_morphism_uniqueness hGD hDR hDC F 𝔠 R I n J X N hN m)

end GlobalTheory.JetLiftMain
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_admissible_connection : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    ∃ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  atlas_forward_decl GlobalTheory.JetLiftMain.exists_jetLift
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetGen

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_gen_of_basis {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module B L'] {g : ℕ}
    (e : Module.Basis (Fin g) R L) (e' : Module.Basis (Fin g) B L') (φ : L →ₛₗ[algebraMap R B] L') (hφ : ∀ j, φ (e j) = e' j)
    (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧ ∀ v, δ' (fun j ↦ φ (v j)) = algebraMap R B (δ v) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hδ ▸ Submodule.mem_top : e.det ∈ Submodule.span R {δ})
  have h1 : c * δ e = 1 := by
    have := congrArg (fun f : L [⋀^Fin g]→ₗ[R] R ↦ f e) hc
    simpa [Module.Basis.det_self] using this
  refine ⟨algebraMap R B (δ e) • e'.det, eq_top_iff.2 fun ω _ ↦ Submodule.mem_span_singleton.2
    ⟨ω e' * algebraMap R B c, ?_⟩, fun v ↦ ?_⟩
  · rw [smul_smul, _root_.mul_assoc, ← map_mul, h1, map_one, _root_.mul_one, ← ω.eq_smul_basis_det e']
  · have hr : ∀ (x : L) (i : Fin g), e'.repr (φ x) i = algebraMap R B (e.repr x i) := fun x i ↦ by
      have : φ x = ∑ j, algebraMap R B (e.repr x j) • e' j := by
        conv_lhs => rw [← e.sum_repr x, map_sum]
        simp only [LinearMap.map_smulₛₗ, hφ]
      rw [this, e'.repr_sum_self]
    have hm : e'.toMatrix (fun j ↦ φ (v j)) = (algebraMap R B).mapMatrix (e.toMatrix v) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hr]
    conv_rhs => rw [δ.eq_smul_basis_det e]
    simp only [AlternatingMap.smul_apply, smul_eq_mul, map_mul, Module.Basis.det_apply, hm, RingHom.map_det]

theorem exists_gen_quot {H H' L L' : Type*} [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module B H'] [AddCommGroup L]
    [Module R L] [AddCommGroup L'] [Module B L'] {K I : Type*} [Fintype K] [Fintype I] {g : ℕ}
    (b : Module.Basis K R H) (b' : Module.Basis K B H') (bc : H →ₛₗ[algebraMap R B] H') (hb : ∀ k, bc (b k) = b' k)
    (t : I → B) (N : I → Module.End R H) (hN : ∀ i j, N i * N j = 0) (q : H →ₗ[R] L) (hq : Function.Surjective q)
    (q' : H' →ₗ[B] L') (hq' : Function.Surjective q')
    (hker : LinearMap.ker q' = Submodule.span B {d | ∃ x ∈ LinearMap.ker q, d = bc x + ∑ i, t i • bc (N i x)})
    (e : Module.Basis (Fin g) R L) (δ : L [⋀^Fin g]→ₗ[R] R) (hδ : Submodule.span R {δ} = ⊤) :
    ∃ δ' : L' [⋀^Fin g]→ₗ[B] B, Submodule.span B {δ'} = ⊤ ∧
      ∀ x : Fin g → H, δ' (fun j ↦ q' (bc (x j) + ∑ i, t i • bc (N i (x j)))) = algebraMap R B (δ fun j ↦ q (x j)) := by
  have hNN : ∀ i j x, N i (N j x) = 0 := fun i j x ↦ LinearMap.congr_fun (hN i j) x
  let nn : H →ₛₗ[algebraMap R B] H' :=
    { toFun x := bc x + ∑ i, t i • bc (N i x)
      map_add' x y := by
        simp only [map_add, smul_add, Finset.sum_add_distrib]; abel
      map_smul' r x := by
        simp only [map_smul, LinearMap.map_smulₛₗ, smul_add, Finset.smul_sum, smul_smul, mul_comm] }
  have nn_def : ∀ x, nn x = bc x + ∑ i, t i • bc (N i x) := fun _ ↦ rfl
  have nnN : ∀ i x, nn (N i x) = bc (N i x) := fun i x ↦ by simp [nn_def, hNN]
  have bc_eq : ∀ x, bc x = nn x - ∑ i, t i • nn (N i x) := fun x ↦ by simp only [nnN, nn_def x, add_sub_cancel_right]
  let φ : L →ₛₗ[algebraMap R B] L' :=
    ((LinearMap.ker q).liftQ (q' ∘ₛₗ nn) fun x hx ↦ by
      change nn x ∈ LinearMap.ker q'
      rw [hker]
      exact Submodule.subset_span ⟨x, hx, rfl⟩) ∘ₛₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hφ : ∀ x, φ (q x) = q' (nn x) := fun x ↦ by
    have : (q.quotKerEquivOfSurjective hq).symm (q x) = Submodule.Quotient.mk x :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have ext : ∀ l : H →ₗ[R] R, ∃ l' : H' →ₗ[B] B, ∀ x, l' (bc x) = algebraMap R B (l x) := fun l ↦
    ⟨b'.constr B fun k ↦ algebraMap R B (l (b k)), fun x ↦ by
      have h : ∀ k, (b'.constr B fun k ↦ algebraMap R B (l (b k))) (b' k) = algebraMap R B (l (b k)) :=
        fun k ↦ b'.constr_basis B _ k
      conv_lhs => rw [← b.sum_repr x, map_sum, map_sum]
      conv_rhs => rw [← b.sum_repr x, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [bc.map_smulₛₗ, map_smul, hb, h, map_smul, smul_eq_mul, smul_eq_mul, map_mul]⟩
  have coord : ∀ l : L →ₗ[R] R, ∃ l' : L' →ₗ[B] B, ∀ v, l' (φ v) = algebraMap R B (l v) := fun l ↦ by
    obtain ⟨l₀, h₀⟩ := ext (l ∘ₗ q)
    choose l₁ h₁ using fun i ↦ ext (l ∘ₗ q ∘ₗ N i)
    let ξ : H' →ₗ[B] B := l₀ - ∑ i, t i • l₁ i
    have hξ : ∀ x, ξ (nn x) = algebraMap R B (l (q x)) := fun x ↦ by
      simp [ξ, nn_def, LinearMap.sum_apply, map_sum, h₀, h₁, hNN]
    have hk : LinearMap.ker q' ≤ LinearMap.ker ξ := by
      rw [hker, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      change ξ (nn x) = 0
      rw [hξ, LinearMap.mem_ker.1 hx, map_zero, map_zero]
    refine ⟨(LinearMap.ker q').liftQ ξ hk ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap, fun v ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hq v
    have : (q'.quotKerEquivOfSurjective hq').symm (q' (nn x)) = Submodule.Quotient.mk (nn x) :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    simp only [hφ, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply, hξ]
  have li : LinearIndependent B fun j ↦ φ (e j) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    obtain ⟨l', hl'⟩ := coord (e.coord j)
    have := congrArg l' hc
    simpa [map_sum, hl', Finsupp.single_apply, apply_ite (algebraMap R B)] using this
  have sp : ⊤ ≤ Submodule.span B (Set.range fun j ↦ φ (e j)) := by
    have h1 : ∀ v, φ v ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun v ↦ by
      rw [← e.sum_repr v, map_sum]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have h2 : ∀ x, q' (bc x) ∈ Submodule.span B (Set.range fun j ↦ φ (e j)) := fun x ↦ by
      rw [bc_eq, map_sub, map_sum, ← hφ]
      refine sub_mem (h1 _) (Submodule.sum_mem _ fun i _ ↦ ?_)
      rw [map_smul, ← hφ]
      exact Submodule.smul_mem _ _ (h1 _)
    intro w _
    obtain ⟨d, rfl⟩ := hq' w
    rw [← b'.sum_repr d, map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [map_smul, ← hb]
    exact Submodule.smul_mem _ _ (h2 _)
  obtain ⟨δ', h1, h2⟩ := exists_gen_of_basis e (Module.Basis.mk li sp) φ (fun j ↦ by simp) δ hδ
  refine ⟨δ', h1, fun x ↦ ?_⟩
  rw [← h2]
  simp only [hφ, nn_def]

end Alg

theorem nonempty_basis_lie (H : GlobalTheory.Published.AbelianDeRham.Hodge) {R : Type} [CommRing R] [IsLocalRing R] {A : Over (Sp R)} [GrpObj A]
    [IsCommMonObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {O : Type} [CommRing O]
    (a : OAct O A) : Nonempty (Module.Basis (Fin g) R (Serre.Lie a)) := by
  obtain ⟨hL, ⟨M, hM⟩, h1, h2, h3⟩ := H R A g hA hg
  haveI : Module.Free R (PrimitiveSubmodule A) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank R (PrimitiveSubmodule A) = g := by
    have := h3 (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hs : Function.Surjective (PrimitiveSubmodule A).dualRestrict := fun l ↦
    ⟨l ∘ₗ (PrimitiveSubmodule A).projectionOnto M hM, LinearMap.ext fun c ↦ by simp⟩
  let E : (HdR A ⧸ Fil A) ≃ₗ[R] Module.Dual R (PrimitiveSubmodule A) :=
    (Submodule.quotEquivOfEq _ _ (Submodule.dualRestrict_ker_eq_dualAnnihilator _).symm).trans
      ((PrimitiveSubmodule A).dualRestrict.quotKerEquivOfSurjective hs)
  exact ⟨(Module.finBasisOfFinrankEq R _ hr).dualBasis.map (E.symm.trans (hL.quotEquiv a))⟩

theorem main : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC →
    ∀ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} →
      ∃ δ' : X'.DetGen, ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
        (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
        (∀ j, IsJetElt J X N m (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
          δ'.1 v' = algebraMap R J.B (δ.1 v) := by
  intro _ H _ F _ _ _ 𝔠 R _ _ _ _ I _ n J X δ N hN m hm X' i pull hfil
  classical
  obtain ⟨e⟩ := nonempty_basis_lie H.2.1 X.ab X.dim X.rm
  obtain ⟨f1, f2, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  let p := Module.Free.chooseBasis R (primDR X.A)
  let p' := (Algebra.TensorProduct.basis J.B p).map (LinearEquiv.ofBijective _ hm)
  have hp : ∀ k, p' k = m.pull (p k) := fun k ↦ by
    simp only [p', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact (liftSemi_tmul m.pull 1 (p k)).trans (one_smul _ _)
  have hc : ∀ x c, hm.bcMap x (m.pull c) = algebraMap R J.B (x c) := fun x ↦ hm.corr_iff.2 rfl
  have hb : ∀ k, hm.bcMap (p.dualBasis k) = p'.dualBasis k := fun k ↦ p'.ext fun l ↦ by
    rw [Module.Basis.dualBasis_apply_self, hp, hc, Module.Basis.dualBasis_apply_self]
    split_ifs <;> simp
  have hj : ∀ x d, IsJetElt J X N m x d ↔ d = hm.bcMap x + ∑ i, J.t i • hm.bcMap (N i x) := fun x d ↦ by
    constructor
    · intro h
      refine p'.ext fun l ↦ ?_
      rw [hp, h]
      simp [LinearMap.sum_apply, hc]
    · rintro rfl c
      simp [LinearMap.sum_apply, hc]
  have hπ : Function.Surjective J.π := fun r ↦ ⟨r • J.b ⟨0, by simp⟩, by simp [J.π_eq]⟩
  have hbij := GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective H.2.2.2.1 X'.ab X'.dim J.nil hπ rfl pull.grp
  have hL := (H.2.1 R X.A _ X.ab X.dim).1
  have hL' := (H.2.1 J.B X'.A _ X'.ab X'.dim).1
  obtain ⟨δ', h1, h2⟩ := exists_gen_quot p.dualBasis p'.dualBasis hm.bcMap hb J.t N hN.2.1 (hL.toLie X.rm)
    (hL.toLie_surjective _) (hL'.toLie X'.rm ∘ₗ crysToDR J.κ pull.grp) ((hL'.toLie_surjective _).comp hbij.2)
    (by
      rw [LinearMap.ker_comp, hL'.ker_toLie, hL.ker_toLie]
      simp only [← hj]
      exact hfil) e δ.1 δ.2
  refine ⟨⟨δ', h1⟩, fun x d v v' h ↦ ?_⟩
  obtain rfl : v = fun j ↦ hL.toLie X.rm (x j) := funext fun j ↦ ((hL.toLie_eq_iff _).2 (h j).2.1).symm
  rw [← h2]
  refine congrArg δ' (funext fun j ↦ ?_)
  rw [← (hj _ _).1 (h j).1]
  exact ((hL'.toLie_eq_iff _).2 (h j).2.2).symm

end GlobalTheory.JetGen
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_morphism_determinant_generator : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) (δ : X.DetGen)
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC →
    ∀ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} →
      ∃ δ' : X'.DetGen, ∀ (x : Fin (Module.finrank ℚ F) → HdR X.A) (d : Fin (Module.finrank ℚ F) → Crys J.κ (spMap J.π) X.A)
        (v : Fin (Module.finrank ℚ F) → X.Lie) (v' : Fin (Module.finrank ℚ F) → X'.Lie),
        (∀ j, IsJetElt J X N m (x j) (d j) ∧ IsLieImage (x j) (v j).hom ∧ IsLieImage (crysToDR J.κ pull.grp (d j)) (v' j).hom) →
          δ'.1 v' = algebraMap R J.B (δ.1 v) := by
  atlas_forward_decl GlobalTheory.JetGen.main
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

theorem jetConstMor {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type}
    [Fintype I] {n : ℕ} (J : JetRing R I n) (X : Obj F 𝔠 (Sp R)) :
    GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)) := by
  have e : J.π.comp (algebraMap R J.B) = RingHom.id R := by
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply, J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul]
    exact mul_one r
  refine GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _) ?_ (𝟙 X.A)
  rw [← Cris.spMap_comp, e, Cris.spMap_id]

theorem jetLift_of_deformation_of_deRham (hGD : GlobalTheory.Published.GrothendieckDeformation) (hDR : GlobalTheory.Published.AbelianDeRham)
    (hDC : GlobalTheory.Published.AbelianDualCrystal) : JetLift := by
  intro F _ _ _ 𝔠 R _ _ _ _ I _ n J X δ N hN
  have m := jetConstMor J X
  obtain ⟨X', i, pull, hF⟩ := GlobalTheory.T.jet_morphism_admissible_connection hGD hDR hDC F 𝔠 R I n J X N hN m
  obtain ⟨δ', hδ⟩ := GlobalTheory.T.jet_morphism_determinant_generator hGD hDR hDC F 𝔠 R I n J X δ N hN m
    (GlobalTheory.T.jet_group_morphism_base_change hGD hDR hDC F 𝔠 R I n J X m) X' i pull hF
  exact ⟨⟨X', i, pull, m, δ', fun x hx d hd ↦ hF ▸ Submodule.subset_span ⟨x, hx, hd⟩, hδ⟩⟩

end GlobalTheory.LatJet
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_lift_of_deformation_de_rham : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → JetLift := by
  atlas_forward_decl GlobalTheory.LatJet.jetLift_of_deformation_of_deRham
end
