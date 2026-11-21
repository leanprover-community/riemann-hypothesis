import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmUniformization
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmConjugation

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.UnifOffOrigin

theorem exists_totPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h
    apply 𝔠.ne_zero
    exact (FractionalIdeal.coeToSubmodule_eq_bot).mp h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 := by
    rw [hy, Algebra.smul_def]
    exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0
  refine ⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  intro τ
  have hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y := by
    rw [mul_comm a y, mul_smul, ← hy, Algebra.smul_def]
  show 0 < τ ((a * y) • x)
  rw [hval, map_mul]
  have : τ (algebraMap (𝓞 F) F y) ≠ 0 := (map_ne_zero τ).mpr hy0
  exact mul_self_pos.mpr this

theorem exists_affine_mem_mem {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    (p q : X.A.left) : ∃ W : X.A.left.Opens, IsAffineOpen W ∧ p ∈ W ∧ q ∈ W := by
  obtain ⟨c, hc⟩ := exists_totPos 𝔠
  have hL : ((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).IsLB := LB.isLB_pull (X.isLB c) _
  have hA := isAmpleLB_of_relAmple_of_isAffine X.A hL (X.pos c hc)
  obtain ⟨_, -, s, hS, -, ha⟩ := hA.exists_affine_finite_subset (S := {p, q}) (Set.toFinite _) (U := ⊤)
    (fun _ _ => trivial)
  exact ⟨_, ha, hS (by simp), hS (by simp)⟩

theorem eq_zero_of_isDiff_of_not_isTangent : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left) (n : ℕ)
    (u : HolUnif X.A L n) (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A), u.IsDiff w v → ¬ IsTangent v → w = 0 := by
  intro F _ _ 𝔠 X L n u w v hd hv
  let pt : PrimeSpectrum ℂ := default
  obtain ⟨W, hW, hx, h0⟩ := exists_affine_mem_mem X ((spMap TangentOrigin.fstC ≫ v.left) pt) ((u.ex 0).left pt)
  have hx' : ⊤ ≤ (spMap TangentOrigin.fstC ≫ v.left) ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 hx
  have h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 h0
  have hv' : ⊤ ≤ v.left ⁻¹ᵁ W := (TangentOrigin.top_le_preimage_iff v.left W).2 hx'
  have hsnd : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).snd =
      (TangentOrigin.jet u w W h0' f).snd := fun f => hd W hv' f
  have hfst : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).fst =
      TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f := fun f =>
    (TangentOrigin.evalPt_spMap_comp _ v.left W hv' hx' f).symm
  have key : ∀ f, (TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f -
      TangentOrigin.evalPt (u.ex 0).left W h0' f) * (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    have e := hsnd (f * f)
    rw [map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, hsnd f, hfst f,
      TangentOrigin.jet_fst] at e
    linear_combination e / 2
  obtain ⟨h, hh⟩ : ∃ h, TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' h ≠
      TangentOrigin.evalPt (u.ex 0).left W h0' h := by
    by_contra hc
    push_neg at hc
    exact hv ((TangentOrigin.ext_evalPt hW hx' h0' (RingHom.ext hc)).trans (TangentOrigin.ex_zero_left u))
  have hdh : (TangentOrigin.jet u w W h0' h).snd = 0 := (mul_eq_zero.1 (key h)).resolve_left (sub_ne_zero.2 hh)
  have hδ : ∀ f, (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    by_cases hf : TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f =
        TangentOrigin.evalPt (u.ex 0).left W h0' f
    · have k2 := key (f + h)
      rw [map_add, map_add, hf, add_sub_add_left_eq_sub] at k2
      have e := (mul_eq_zero.1 k2).resolve_left (sub_ne_zero.2 hh)
      rwa [map_add, TrivSqZeroExt.snd_add, hdh, add_zero] at e
    · exact (mul_eq_zero.1 (key f)).resolve_left (sub_ne_zero.2 hf)
  have ht := ArchMetricCompare.isTangent_zero X.A
  have h₁ := (TangentOrigin.tangent_mem_iff (u := u) ht W).2 h0'
  refine ArchMetricCompare.eq_zero_of_isDiff u ((TangentOrigin.isDiff_iff ht hW h₁ h0' w).2
    (RingHom.ext fun f => TrivSqZeroExt.ext (TangentOrigin.tangent_fst ht h₁ h0' f) ?_))
  have e := ArchMetricCompare.isDiff_zero u W h₁ f
  rw [map_zero] at e
  exact e.trans (hδ f).symm

end GlobalTheory.UnifOffOrigin
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differential_zero_of_not_tangent : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left) (n : ℕ)
    (u : HolUnif X.A L n) (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A), u.IsDiff w v → ¬ IsTangent v → w = 0 := by
  atlas_forward_decl GlobalTheory.UnifOffOrigin.eq_zero_of_isDiff_of_not_isTangent
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem isDiff_zero_of_isGrpPullback : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  intro A A' _ _ p g h L L' n n' u u' v v' e hd U hU f
  haveI : IsIso (spMap (g : ℂ →+* ℂ)) :=
    (inferInstance : IsIso (Spec.map (g.toCommRingCatIso).hom))
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := by
    refine (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).2 fun q _ => ?_
    have hq := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hU (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hs : ∀ a b : PrimeSpectrum (DualNumber ℂ), a = b := fun a b => by
      obtain ⟨a, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective a
      obtain ⟨b, rfl⟩ := GlobalTheory.TangentOrigin.spMap_fst_surjective b
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) a b]
    rw [e2] at hq
    change v.left (spMap GlobalTheory.TangentOrigin.fstC q) ∈ inv p ⁻¹ᵁ U
    rw [hs (spMap GlobalTheory.TangentOrigin.fstC q)
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) (spMap GlobalTheory.TangentOrigin.fstC q))]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv p).app U).hom f)
  rw [map_zero] at e3 ⊢
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact (congrArg (g : ℂ →+* ℂ) e3).trans (map_zero _)

end GlobalTheory.ConjTangent
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_uniformization_differential_zero : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (n n' : ℕ) (u : HolUnif A L n)
    (u' : HolUnif A' L' n') (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
    v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff 0 v → u'.IsDiff 0 v' := by
  atlas_forward_decl GlobalTheory.ConjTangent.isDiff_zero_of_isGrpPullback
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConjTangentSemilin

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {p : A'.left ⟶ A.left} {g : ℂ ≃+* ℂ}

theorem isIso_spMap (g : ℂ ≃+* ℂ) : IsIso (spMap (g : ℂ →+* ℂ)) := by
  have : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) :=
    ⟨⟨CommRingCat.ofHom (g.symm : ℂ →+* ℂ), by ext; simp, by ext; simp⟩⟩
  unfold spMap
  infer_instance

theorem snd_pull [IsIso p] {L : LB A.left} {N : ℕ} (u : HolUnif A L N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'}
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (U : A'.left.Opens) (hU : ⊤ ≤ v'.left ⁻¹ᵁ U) (f : Γ(A'.left, U)) :
    (TangentOrigin.evalPt (R := DualNumber ℂ) v'.left U hU f).snd =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w) := by
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫
      (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) q)]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  rw [k _ hU e2]
  have e3 := hd _ h2 (((inv p).app U).hom f)
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg g e3

def Rel {L : LB A.left} {L' : LB A'.left} {N : ℕ} (p : A'.left ⟶ A.left) [IsIso p] (g : ℂ ≃+* ℂ)
    (u : HolUnif A L N) (u' : HolUnif A' L' N) (w' w : Fin N → ℂ) : Prop :=
  ∀ (U : A'.left.Opens), ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U → ∀ f : Γ(A'.left, U),
    fderiv ℂ (fun z => valAt' (u'.ex z).left U f) 0 w' =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w)

theorem isDiff_iff_rel [IsIso p] (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) {L : LB A.left} {L' : LB A'.left}
    {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'} (hv : IsTangent v)
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (w' : Fin N → ℂ) : u'.IsDiff w' v' ↔ Rel p g u u' w' w := by
  have hv' : IsTangent v' := isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h hv e
  constructor
  · intro hd' U hU f
    have hU' := (TangentOrigin.tangent_mem_iff (u := u') hv' U).2 hU
    exact (hd' U hU' f).symm.trans (snd_pull u e hd U hU' f)
  · intro hr U hU f
    exact (snd_pull u e hd U hU f).trans
      (hr U ((TangentOrigin.tangent_mem_iff (u := u') hv' U).1 hU) f).symm

theorem rel_add [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w₁' w₁ w₂' w₂ : Fin N → ℂ} (h₁ : Rel p g u u' w₁' w₁) (h₂ : Rel p g u u' w₂' w₂) :
    Rel p g u u' (w₁' + w₂') (w₁ + w₂) := fun U hU f => by
  rw [map_add, map_add, map_add, h₁ U hU f, h₂ U hU f]

theorem rel_smul [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w' w : Fin N → ℂ} (c : ℂ) (h₁ : Rel p g u u' w' w) : Rel p g u u' (g c • w') (c • w) := fun U hU f => by
  rw [map_smul, map_smul, h₁ U hU f, smul_eq_mul, smul_eq_mul, map_mul]

theorem pull_sq (g : ℂ ≃+* ℂ) (v : epsR ℂ ⟶ A) :
    (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
  rw [Category.assoc, Over.w]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def liftT (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ A' :=
  Over.homMk (h.1.lift _ _ (pull_sq g v)) (h.1.lift_snd _ _ _)

theorem liftT_left (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) :
    (liftT h v).left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left :=
  h.1.lift_fst _ _ _

theorem exists_semilinear_transport : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (N : ℕ) (u : HolUnif A L N)
    (u' : HolUnif A' L' N), (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) →
    ∃ T : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ), Function.Injective T ∧
      ∀ (w : Fin N → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), IsTangent v →
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v → u'.IsDiff (T w) v' := by
  intro A A' _ _ p g h L L' N u u' hex huniq
  haveI := isIso_spMap g
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  choose vv hvv using fun w => (hex w).exists
  have ht : ∀ w, IsTangent (liftT h (vv w)) := fun w =>
    isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h (hvv w).1 (liftT_left h _)
  choose T hT using fun w => (huniq _ (ht w)).exists
  have hR : ∀ w, Rel p g u u' (T w) w := fun w =>
    (isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).1 (hT w)
  have hU : ∀ w w', Rel p g u u' w' w → T w = w' := fun w w' hr =>
    (huniq _ (ht w)).unique (hT w) ((isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).2 hr)
  let Tl : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ) :=
    { toFun := T
      map_add' := fun a b => hU _ _ (rel_add u u' (hR a) (hR b))
      map_smul' := fun c a => hU _ _ (rel_smul u u' c (hR a)) }
  refine ⟨Tl, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Tl).2 fun w hw => ?_
    have hw' : T w = 0 := hw
    have h0 : u'.IsDiff 0 (liftT h (vv w)) := by rw [← hw']; exact hT w
    have e1 := eq_of_isDiff u' (ht w) (isTangent_zero A') h0 (isDiff_zero u')
    have e2 := (zero_pull_iff (σ := (g : ℂ →+* ℂ)) h (liftT_left h (vv w))).1 e1
    have hd := (hvv w).2
    rw [e2] at hd
    exact eq_zero_of_isDiff u hd
  · intro w v v' hv e hd
    exact (isDiff_iff_rel h u u' hv e hd _).2 (hR w)

end GlobalTheory.ConjTangentSemilin
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_uniformization_semilinear_map : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (N : ℕ) (u : HolUnif A L N)
    (u' : HolUnif A' L' N), (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) →
    ∃ T : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ), Function.Injective T ∧
      ∀ (w : Fin N → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), IsTangent v →
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v → u'.IsDiff (T w) v' := by
  atlas_forward_decl GlobalTheory.ConjTangentSemilin.exists_semilinear_transport
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem exists_conj_holUnif_tangent : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X X' : Obj F 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ X.A.left) (g : ℂ ≃+* ℂ)
    (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p →
    ∃ u' : HolUnif X'.A (X'.diag c) n, ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v →
        u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
  intro _ _ _ F _ _ 𝔠 X X' p g c n u Ω₀ Ω₁ h0 h1 hX
  have hn := Obj.holUnif_dim_eq X u
  subst hn
  obtain ⟨L₁, u₁, -, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X'
  obtain ⟨u₀, -, -, -, -⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif X'.A X'.ab L₁ _ u₁ (X'.diag c)
    (pull_isLB (X'.isLB c) _)
  obtain ⟨-, hu⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨hu₀, -⟩ := GlobalTheory.TorusTransfer.tangent_bijective u₀ X'.dim
  obtain ⟨T, hTi, hT⟩ := GlobalTheory.T.conjugate_uniformization_semilinear_map X.A X'.A p g hX.grp _ _ _ u u₀ hu hu₀
  let ψ : (Fin (Module.finrank ℚ F) → ℂ) → (Fin (Module.finrank ℚ F) → ℂ) :=
    fun w' => Ω₀⁻¹ • fun j => g.symm (Ω₁ * w' j)
  have hψa : ∀ a b, ψ (a + b) = ψ a + ψ b := fun a b => by
    simp only [ψ, ← smul_add]
    congr 1
    ext j
    simp [mul_add]
  have hψs : ∀ (a : ℂ) b, ψ (a • b) = g.symm a • ψ b := fun a b => by
    simp only [ψ, smul_comm (g.symm a) Ω₀⁻¹]
    congr 1
    ext j
    simp [mul_left_comm]
  let φl : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := fun w' => T (ψ w')
      map_add' := fun a b => by simp only [hψa, map_add]
      map_smul' := fun a b => by
        simp only [hψs, map_smulₛₗ, RingHom.id_apply]
        congr 1
        simp }
  have hinj : Function.Injective φl := by
    intro a b hab
    have hab' := hTi hab
    simp only [ψ] at hab'
    have := smul_right_injective _ (inv_ne_zero h0) hab'
    ext j
    have e := congrFun this j
    simp only [EmbeddingLike.apply_eq_iff_eq] at e
    exact mul_left_cancel₀ h1 e
  let φ := LinearEquiv.ofInjectiveEndo φl hinj
  obtain ⟨u', -, -, -, -, hD⟩ := GlobalTheory.exists_holUnif_reparam X'.A (X'.diag c) _ u₀ φ (fun _ => 1)
    (differentiable_const 1) (fun _ => one_ne_zero) rfl
  refine ⟨u', fun w v v' hv hd => hD _ _ ?_⟩
  by_cases ht : IsTangent v
  · have e : φ (fun j => g (Ω₀ * w j) / Ω₁) = T w := by
      show T (ψ _) = T w
      congr 1
      ext j
      simp only [ψ, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_cancel₀ _ h1, RingEquiv.symm_apply_apply]
      field_simp
    rw [e]
    exact hT w v v' ht hv hd
  · have hw := GlobalTheory.T.differential_zero_of_not_tangent F 𝔠 X _ _ u w v hd ht
    subst hw
    have e : φ (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
      have : (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
        ext j
        simp
      rw [this, map_zero]
    rw [e]
    exact GlobalTheory.T.conjugate_uniformization_differential_zero X.A X'.A p g hX.grp _ _ _ _ u u₀ v v' hv hd

end GlobalTheory.ConjTangent
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conjugate_holomorphic_uniformization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X X' : Obj F 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ X.A.left) (g : ℂ ≃+* ℂ)
    (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p →
    ∃ u' : HolUnif X'.A (X'.diag c) n, ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v →
        u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
  atlas_forward_decl GlobalTheory.ConjTangent.exists_conj_holUnif_tangent
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.ApproxHatO

theorem exists_sub_mul_mem_hatO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro E _ _ _ c hc y z
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set u : Af E := algebraMap E (Af E) (N : E)⁻¹ with hu
  set U : Set (Af E) := {a | ∀ v, (u * a * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E} with hU
  have hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      fun _ => Valued.isOpen_valuationSubring _
  have hV : IsOpen {x' : Af E | z - x' ∈ U} :=
    hO.preimage (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const))
  have hz : z ∈ {x' : Af E | z - x' ∈ U} := by
    show ∀ v, (u * (z - z) * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E
    intro v
    rw [sub_self, mul_zero, zero_mul]
    exact zero_mem _
  obtain ⟨x, hx⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨z, hz⟩
  refine ⟨x, ?_⟩
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := u * (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E)) hx
  have e : algebraMap E (Af E) (algebraMap (OF E) E (N : OF E)) * u = 1 := by
    rw [map_natCast, hu, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  rwa [← mul_assoc, ← mul_assoc, e, one_mul] at key

end GlobalTheory.CMVal.ApproxHatO
end

open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_approximation_mod_conductor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  atlas_forward_decl GlobalTheory.CMVal.ApproxHatO.exists_sub_mul_mem_hatO
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IntMult

theorem exists_mul_mem_hatO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  intro E _ _ _ c hc a
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hnc : ((Ideal.absNorm c : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  have hy : ∀ v : HeightOneSpectrum (𝓞 E),
      (algebraMap E (Af E) (algebraMap (𝓞 E) E b) * a) v ∈ v.adicCompletionIntegers E := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hb v)
  have h := PicFin.mul_mem_hatO hnc hy
  refine ⟨algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E) * algebraMap (𝓞 E) E b, ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · rw [map_natCast]; exact_mod_cast hN
    · simpa using hb0
  · rwa [map_mul, mul_assoc]

end GlobalTheory.CMVal.IntMult
end

open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_clear_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  atlas_forward_decl GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO
end

section
section
open Module

namespace GlobalTheory

theorem sublattice_of_full_rank_quotient_torsion : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  intro n Λ Λ₂ M hΛ hΛ₂ hsΛ hsΛ₂ hM hr w hw
  haveI : IsZLattice ℝ Λ := ⟨hsΛ⟩
  haveI : IsZLattice ℝ Λ₂ := ⟨hsΛ₂⟩
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  haveI : Module.Finite ℤ Λ₂ := ZLattice.module_finite ℝ Λ₂
  have e1 : finrank ℤ Λ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ
  have e2 : finrank ℤ Λ₂ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ₂
  set M' : Submodule ℤ Λ := M.comap Λ.subtype with hM'
  have hMM : Module.rank ℤ M' = Module.rank ℤ M := (Submodule.comapSubtypeEquivOfLe hM).rank_eq
  have hΛr : Module.rank ℤ Λ = (finrank ℤ Λ : Cardinal) := (Module.finrank_eq_rank ℤ Λ).symm
  have hΛ₂r : Module.rank ℤ Λ₂ = (finrank ℤ Λ₂ : Cardinal) := (Module.finrank_eq_rank ℤ Λ₂).symm
  have hle : Module.rank ℤ M' ≤ Module.rank ℤ Λ := Submodule.rank_le M'
  have hge : Module.rank ℤ Λ ≤ Module.rank ℤ M' := by
    rw [hMM, hΛr, e1, ← e2, ← hΛ₂r]; exact hr
  have heq : Module.rank ℤ M' = Module.rank ℤ Λ := le_antisymm hle hge
  have hsum := rank_quotient_add_rank_of_isDomain M'
  haveI : Module.Finite ℤ M' := Module.Finite.of_injective M'.subtype M'.injective_subtype
  rw [heq, hΛr, ← Module.finrank_eq_rank ℤ (Λ ⧸ M')] at hsum
  have h0 : finrank ℤ (Λ ⧸ M') = 0 := by
    have : ((finrank ℤ (Λ ⧸ M') + finrank ℤ Λ : ℕ) : Cardinal) = (finrank ℤ Λ : Cardinal) := by
      push_cast; exact hsum
    have := Nat.cast_injective this
    omega
  have htor : Module.IsTorsion ℤ (Λ ⧸ M') := Module.finrank_eq_zero_iff_isTorsion.1 h0
  obtain ⟨⟨k, hk⟩, hx⟩ := htor (x := Submodule.Quotient.mk (⟨w, hw⟩ : Λ))
  refine ⟨k, nonZeroDivisors.ne_zero hk, ?_⟩
  have : (k • (⟨w, hw⟩ : Λ)) ∈ M' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hx
  simpa [hM'] using this

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_multiple_mem_sublattice : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  atlas_forward_decl GlobalTheory.sublattice_of_full_rank_quotient_torsion
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjUnifLattice

theorem lattice_of_conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) → (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) := by
  intro _ _ _ K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hio c y hc 𝔠 T X' p hp u' H

  have hex0 : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {m : ℕ} (u : HolUnif A L m), u.ex 0 = 1 := by
    intro A _ L m u
    have h := u.ex_add 0 0
    rw [add_zero] at h
    simpa using h

  have hpb : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ X'.A, a.left ≫ p = b.left ≫ p → a = b := by
    intro a b h
    exact Over.OverMorphism.ext (hp.grp.1.hom_ext h (by rw [Over.w a, Over.w b]))

  have hepi : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ T.X.A, spMap (g : ℂ →+* ℂ) ≫ a.left = spMap (g : ℂ →+* ℂ) ≫ b.left → a = b := by
    intro a b h
    haveI : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) := (RingEquiv.toCommRingCatIso g).isIso_hom
    haveI : IsIso (spMap (g : ℂ →+* ℂ)) := by unfold spMap; infer_instance
    exact Over.OverMorphism.ext ((cancel_epi _).1 h)
  have H0 : (u'.ex 0).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex 0).left := by
    have := H 0 0 (by simp)
    simp only [map_zero] at this
    exact this

  have hmemL : ∀ x' : E, x' ∈ lattice c (y * (upIdele K E t)⁻¹) ↔
      ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) 0) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro x'
    have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
    show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c ↔ _
    rw [e, Units.val_mul, map_zero, sub_zero]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hdef : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) =
      fun j ↦ g (φ (T.U.e j) x) := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdef0 : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (T.U.e j)) = fun j ↦ φ (T.U.e j) x := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]

  have hsup : ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹), (fun j ↦ g (φ (T.U.e j) x')) ∈ u'.Λ := by
    intro x' hx'
    have h1 := H 0 x' ((hmemL x').1 hx')
    simp only [map_zero] at h1
    rw [← u'.ker, ← hex0 u']
    refine hpb _ _ ?_
    rw [H0]
    exact h1

  have hsubL : ∀ y₁ : (Af E)ˣ, ∃ S : AddSubgroup E, (S : Set E) = lattice c y₁ := by
    intro y₁
    refine ⟨{ carrier := lattice c y₁, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩
    · intro a b ha hb
      show _ ∈ hatO c
      rw [map_add, add_mul]
      exact add_mem ha hb
    · show _ ∈ hatO c
      rw [map_zero, zero_mul]
      exact zero_mem _
    · intro a ha
      show _ ∈ hatO c
      rw [map_neg, neg_mul]
      exact neg_mem ha
  obtain ⟨SL, hSL⟩ := hsubL y
  obtain ⟨SL', hSL'⟩ := hsubL (y * (upIdele K E t)⁻¹)
  have hpos : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hpos⟩
  let Φ : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ φ (T.U.e j) x
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  let Φ' : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ g (φ (T.U.e j) x)
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  have hΦinj : Function.Injective Φ := fun a b h ↦ (φ (T.U.e j₀)).injective (congrFun h j₀)
  have hΦ'inj : Function.Injective Φ' := fun a b h ↦ (φ (T.U.e j₀)).injective (g.injective (congrFun h j₀))
  have hΛ : T.U.u.Λ = SL.toIntSubmodule.map Φ := by
    ext w
    rw [T.U.lat, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · show x ∈ (SL : Set E)
        rw [hSL]; exact hx
      · rw [hdef0]; rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · rw [← hSL]; exact hx
      · rw [hdef0]; rfl
  let M : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) := SL'.toIntSubmodule.map Φ'
  have hMle : M ≤ u'.Λ := by
    rintro w ⟨x', hx', rfl⟩
    exact hsup x' (by rw [← hSL']; exact hx')
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.T.finite_adele_clear_denominator E c hc (upIdele K E t : Af E)
  have hrank : Module.rank ℤ T.U.u.Λ ≤ Module.rank ℤ M := by
    rw [hΛ, ← (Submodule.equivMapOfInjective _ hΦinj _).rank_eq,
      ← (Submodule.equivMapOfInjective _ hΦ'inj _).rank_eq]
    let mulm : E →ₗ[ℤ] E := (AddMonoidHom.mulLeft m).toIntLinearMap
    have hmulm : Function.Injective mulm := mul_right_injective₀ hm0
    calc Module.rank ℤ SL.toIntSubmodule = Module.rank ℤ (SL.toIntSubmodule.map mulm) :=
          (Submodule.equivMapOfInjective _ hmulm _).rank_eq
      _ ≤ Module.rank ℤ SL'.toIntSubmodule := by
          refine Submodule.rank_mono ?_
          rintro _ ⟨x, hx, rfl⟩
          have hx' : x ∈ lattice c y := by rw [← hSL]; exact hx
          show m * x ∈ (SL' : Set E)
          rw [hSL']
          have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
          show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c
          rw [e, Units.val_mul, map_mul]
          have := mul_mem hm hx'
          convert this using 1
          ring
  intro w
  constructor
  · intro hw
    obtain ⟨k, hk, hkw⟩ := GlobalTheory.T.lattice_multiple_mem_sublattice _ u'.Λ T.U.u.Λ M u'.discrete T.U.u.discrete u'.full T.U.u.full hMle hrank w hw
    obtain ⟨x'', hx'', hx''e⟩ := Submodule.mem_map.1 hkw
    have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
    have hw' : w = Φ' (x'' / k) := by
      apply smul_right_injective (Fin (Module.finrank ℚ (FR E)) → ℂ) hk
      show k • w = k • Φ' (x'' / k)
      rw [← map_zsmul, ← hx''e]
      congr 1
      rw [zsmul_eq_mul, mul_div_cancel₀ _ hk']
    set x' := x'' / k
    obtain ⟨x, hx⟩ := GlobalTheory.T.finite_adele_approximation_mod_conductor E c hc y ((upIdele K E t : Af E) * algebraMap E (Af E) x')
    have h1 := H x x' hx
    have hw1 : u'.ex (fun j ↦ g (φ (T.U.e j) x')) = 1 := (u'.ker _).2 (by rw [hw'] at hw; exact hw)
    rw [hw1, ← hex0 u', H0] at h1
    have h2 := hepi _ _ h1
    have h3 : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (T.U.u.ker _).1 (by rw [← h2, hex0])
    rw [T.U.lat] at h3
    obtain ⟨x₀, hx₀, he⟩ := h3
    rw [hdef0] at he
    have hxx : x = x₀ := (φ (T.U.e j₀)).injective (congrFun he j₀)
    subst hxx
    refine ⟨x', ?_, by rw [hdef]; exact hw'⟩
    rw [hmemL, map_zero, sub_zero]
    have := add_mem hx hx₀
    convert this using 1
    ring
  · rintro ⟨x', hx', rfl⟩
    rw [hdef]
    exact hsup x' hx'

end GlobalTheory.ConjUnifLattice
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_galois_compatible : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) → (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) := by
  atlas_forward_decl GlobalTheory.ConjUnifLattice.lattice_of_conj_unif
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjCMPoint

theorem conjUnif_of_torsTransport : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∃ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E _ _ _ _ I _ φ hCM hφ c y hc 𝔠 T X' p hp
  obtain ⟨u', hu'⟩ := GlobalTheory.T.galois_conjugate_holomorphic_uniformization hPC hDR hDC (FR E) 𝔠 T.X X' p g T.U.c _ T.U.u Ω₀ Ω₁ hTT.1 hTT.2.1 hp
  have htor := GlobalTheory.T.torsion_transport_cm_uniformization hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E I φ hCM hφ c y hc 𝔠 T X' p hp u' hu'
  exact ⟨u', GlobalTheory.T.torsion_transport_galois_compatible hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E I φ hCM hφ c y hc 𝔠 T X' p hp u' htor,
    hu', htor⟩

end GlobalTheory.ConjCMPoint
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_periods : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∃ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  atlas_forward_decl GlobalTheory.ConjCMPoint.conjUnif_of_torsTransport
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.DiagConj
open GlobalTheory.HolHom

theorem fderiv_diag {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (U : X.Opens) (hU : ⊤ ≤ c 0 ⁻¹ᵁ U) (f : Γ(X, U)) :
    fderiv ℂ (fun t => valAt' (c (fun j => m j * t j)) U f) 0 w =
      fderiv ℂ (fun t => valAt' (c t) U f) 0 (fun j => m j * w j) := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hL : HasFDerivAt (fun z : Fin n → ℂ => (fun j => m j * z j)) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m) 0 :=
    (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).hasFDerivAt
  have hg := ((hc U hU).2 f).hasFDerivAt
  rw [← h0] at hg
  have hcomp := HasFDerivAt.comp (0 : Fin n → ℂ) hg hL
  have e1 := congrArg (fun L => L w) hcomp.fderiv
  simp only [Function.comp_def, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    h0] at e1
  exact e1

theorem isDerivAt_diag_iff {n : ℕ} {X : Scheme.{0}} {c : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hc : HolAt c 0)
    (m w : Fin n → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt (fun z => c (fun j => m j * z j)) 0 w v ↔ IsDerivAt c 0 (fun j => m j * w j) v := by
  have h0 : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  unfold IsDerivAt
  simp only [h0]
  refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
  rw [fderiv_diag hc m w U hU f]

theorem spMap_dual_cancel (g : ℂ ≃+* ℂ) {X : Scheme.{0}} (x y : Sp (DualNumber ℂ) ⟶ X)
    (h : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ x = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ y) : x = y := by
  have e0 : (Chart.dualMapR (g.symm : ℂ →+* ℂ)).comp (Chart.dualMapR (g : ℂ →+* ℂ)) = RingHom.id _ := by
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR]
  have e : spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact e0
  have := congrArg (spMap (Chart.dualMapR (g.symm : ℂ →+* ℂ)) ≫ ·) h
  simpa [← Category.assoc, e] using this

theorem diag_endo_iff_conj_diag : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (n : ℕ)
    (u : HolUnif A L n) (u' : HolUnif A' L' n) (g : ℂ ≃+* ℂ) (p : A'.left ⟶ A.left),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    (∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      u.IsDiff w v → u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
    ∀ (m : Fin n → ℂ) (α : A ⟶ A) [IsMonHom α] (α' : A' ⟶ A') [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
      ((∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) ↔ (∀ w, u'.ex (fun j ↦ g (m j) * w j) = u'.ex w ≫ α')) := by
  intro A A' _ _ L L' n u u' g p hp Ω₀ Ω₁ hΩ₀ hΩ₁ htr m α _ α' _ hαp
  have holA : IsHolTo Set.univ (fun z => (u.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u.hol U f
  have holA' : IsHolTo Set.univ (fun z => (u'.ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using u'.hol U f
  have hA : ∀ z, HolAt (fun z => (u.ex z).left) z := fun z => holAt_of_isHolTo holA (Set.mem_univ z)
  have hA' : ∀ z, HolAt (fun z => (u'.ex z).left) z := fun z => holAt_of_isHolTo holA' (Set.mem_univ z)
  have one0 : u.ex 0 = 1 := map_zero_eq_one u.ex_add
  have one0' : u'.ex 0 = 1 := map_zero_eq_one u'.ex_add
  have eta : (u.ex 0).left = η[A].left := by
    rw [one0, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have eta' : (u'.ex 0).left = η[A'].left := by
    rw [one0', Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

  have tan : ∀ w, ∃ v : epsR ℂ ⟶ A, IsDerivAt (fun z => (u.ex z).left) 0 w v.left := by
    intro w
    obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt w
    have hv2 : v ≫ A.hom = (epsR ℂ).hom := by
      have h1 := hv.comp A.hom
      have h2 : (fun t => (u.ex t).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun t => Over.w (u.ex t)
      rw [h2] at h1
      rw [h1.unique (isDerivAt_const (𝟙 (Sp ℂ)) 0 w)]
      simp [constVec]
    exact ⟨Over.homMk v hv2, hv⟩

  have ringSq : spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (g : ℂ →+* ℂ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    apply TrivSqZeroExt.ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have fstSq : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (Chart.dualMapR (g : ℂ →+* ℂ)) =
      spMap (g : ℂ →+* ℂ) ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    apply RingHom.ext; intro a
    simp [Chart.dualMapR]
  have fstAlg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    all_goals (ext1; apply RingHom.ext; intro a; simp)
  have conj : ∀ v : epsR ℂ ⟶ A, ∃ v' : epsR ℂ ⟶ A',
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
    intro v
    have w : (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w v]
      exact ringSq
    exact ⟨Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _⟩
  have conj0 : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (u.ex 0).left →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v'.left = (u'.ex 0).left := by
    intro v v' hv' h0
    apply hp.1.hom_ext
    · rw [Category.assoc, hv', ← Category.assoc, fstSq, Category.assoc, h0, eta, eta',
        GlobalTheory.LieChart.unit_comp_of_isGrpPullback hp]
    · rw [Category.assoc, Over.w v', Over.w (u'.ex 0)]
      exact fstAlg

  have trD : ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      IsDerivAt (fun z => (u.ex z).left) 0 w v.left →
      IsDerivAt (fun z => (u'.ex z).left) 0 (fun j => g (Ω₀ * w j) / Ω₁) v'.left := by
    intro w v v' hv' hv
    have h0' := conj0 v v' hv' hv.1
    have hd : u.IsDiff w v := ((isDerivAt0_iff _ _ _).2 hv).2
    exact (isDerivAt0_iff _ _ _).1 ⟨h0', htr w v v' hv' hd⟩
  have Tsurj : ∀ w' : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j)) j) / Ω₁) = w' := by
    intro w'; funext j
    simp only
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, RingEquiv.apply_symm_apply, mul_div_cancel_left₀ _ hΩ₁]
  have Tmul : ∀ w : Fin n → ℂ, (fun j => g (Ω₀ * (fun j => m j * w j) j) / Ω₁) =
      fun j => g (m j) * (fun j => g (Ω₀ * w j) / Ω₁) j := by
    intro w; funext j
    simp only
    rw [mul_left_comm, map_mul, mul_div_assoc]
  have hz : (fun j => m j * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  have hz' : (fun j => g (m j) * (0 : Fin n → ℂ) j) = 0 := by funext j; simp
  constructor
  · intro hα
    have he : ∀ z w : Fin n → ℂ, u'.ex (fun j => g (m j) * (z + w) j) =
        u'.ex (fun j => g (m j) * z j) * u'.ex (fun j => g (m j) * w j) := by
      intro z w
      rw [← u'.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u'.ex (z + w) ≫ α' = (u'.ex z ≫ α') * (u'.ex w ≫ α') := by
      intro z w
      rw [u'.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u'.ex (fun j => g (m j) * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA' _).precomp (k := fun (t : Fin n → ℂ) j => g (m j) * t j)
          (ContinuousLinearMap.mul ℂ (Fin n → ℂ) (fun j => g (m j))).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u'.ex z ≫ α').left) := by
      have e : (fun z => (u'.ex z ≫ α').left) = (fun z => (u'.ex z).left ≫ α'.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA' z).comp α'.left
    have hd : ∀ U : A'.left.Opens, ⊤ ≤ (u'.ex (fun j => g (m j) * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A'.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u'.ex (fun j => g (m j) * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u'.ex z ≫ α').left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w' => ?_
      obtain ⟨v, hv⟩ := tan (fun j => Ω₀⁻¹ * g.symm (Ω₁ * w' j))
      obtain ⟨v', hv'⟩ := conj v
      have D1 := trD _ v v' hv' hv
      rw [Tsurj] at D1
      have hcα : (fun t => (u.ex t).left ≫ α.left) = fun t => (u.ex (fun j => m j * t j)).left :=
        funext fun t => by rw [hα t]; rfl
      have Dα := hv.comp α.left
      rw [hcα] at Dα
      have Dα' := (isDerivAt_diag_iff (hA 0) m _ _).1 Dα
      have hv'α : (v'.left ≫ α'.left) ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (v.left ≫ α.left) := by
        rw [Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have D2 := trD _ (v ≫ α) (v' ≫ α') hv'α Dα'
      rw [Tmul, Tsurj] at D2
      have D2' := (isDerivAt_diag_iff (hA' 0) (fun j => g (m j)) w' _).2 D2
      have D3 := D1.comp α'.left
      have hU' : ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U := by rw [← hz']; exact hU
      have hU'' : ⊤ ≤ ((u'.ex 0).left ≫ α'.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0', MonObj.one_comp, ← one0']; exact hU'
      have e1 := D2'.2 U hU f
      have e2 := D3.2 U hU'' f
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u'.ex (fun j => g (m j) * w j)) = (fun w => u'.ex w ≫ α') :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w
  · intro hα'
    have he : ∀ z w : Fin n → ℂ, u.ex (fun j => m j * (z + w) j) =
        u.ex (fun j => m j * z j) * u.ex (fun j => m j * w j) := by
      intro z w
      rw [← u.ex_add]
      congr 1
      funext j
      simp [mul_add]
    have he' : ∀ z w : Fin n → ℂ, u.ex (z + w) ≫ α = (u.ex z ≫ α) * (u.ex w ≫ α) := by
      intro z w
      rw [u.ex_add, MonObj.mul_comp]
    have hol : IsHolTo Set.univ (fun (z : Fin n → ℂ) => (u.ex (fun j => m j * z j)).left) :=
      isHolTo_of_holAt isOpen_univ fun z _ =>
        (hA _).precomp (k := fun (t : Fin n → ℂ) j => m j * t j) (ContinuousLinearMap.mul ℂ (Fin n → ℂ) m).differentiableAt
    have hol' : IsHolTo Set.univ (fun z => (u.ex z ≫ α).left) := by
      have e : (fun z => (u.ex z ≫ α).left) = (fun z => (u.ex z).left ≫ α.left) :=
        funext fun z => by rw [Over.comp_left]
      rw [e]
      exact isHolTo_of_holAt isOpen_univ fun z _ => (hA z).comp α.left
    have hd : ∀ U : A.left.Opens, ⊤ ≤ (u.ex (fun j => m j * (0 : Fin n → ℂ) j)).left ⁻¹ᵁ U →
        ∀ f : Γ(A.left, U), fderiv ℂ (fun (z : Fin n → ℂ) => valAt' (u.ex (fun j => m j * z j)).left U f) 0 =
          fderiv ℂ (fun z => valAt' (u.ex z ≫ α).left U f) 0 := by
      intro U hU f
      simp only [Over.comp_left]
      refine ContinuousLinearMap.ext fun w => ?_
      obtain ⟨v, hv⟩ := tan w
      obtain ⟨v', hv'⟩ := conj v
      obtain ⟨v₂, hv₂⟩ := tan (fun j => m j * w j)
      obtain ⟨v₂', hv₂'⟩ := conj v₂
      have D1 := trD w v v' hv' hv
      have hcα' : (fun t => (u'.ex t).left ≫ α'.left) = fun t => (u'.ex (fun j => g (m j) * t j)).left :=
        funext fun t => by rw [hα' t]; rfl
      have D1α := D1.comp α'.left
      rw [hcα'] at D1α
      have D1α' := (isDerivAt_diag_iff (hA' 0) _ _ _).1 D1α
      have D2 := trD _ v₂ v₂' hv₂' hv₂
      rw [Tmul] at D2
      have huq := D2.unique D1α'
      have hv₂α : v₂.left = v.left ≫ α.left := by
        apply spMap_dual_cancel g
        rw [← hv₂', huq, Category.assoc, hαp, ← Category.assoc, hv', Category.assoc]
      have E1 := (isDerivAt_diag_iff (hA 0) m w _).2 hv₂
      have E2 := hv.comp α.left
      have hU' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by rw [← hz]; exact hU
      have hU'' : ⊤ ≤ ((u.ex 0).left ≫ α.left) ⁻¹ᵁ U := by
        rw [← Over.comp_left, one0, MonObj.one_comp, ← one0]; exact hU'
      have e1 := E1.2 U hU f
      have e2 := E2.2 U hU'' f
      rw [hv₂α] at e1
      exact e1.symm.trans e2
    have key : (fun (w : Fin n → ℂ) => u.ex (fun j => m j * w j)) = (fun w => u.ex w ≫ α) :=
      eq_of_fderiv_eq (y := 𝟙 (Sp ℂ)) he he' hol hol' hd
    exact fun w => congrFun key w

end GlobalTheory.DiagConj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_transport_galois_conjugate : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (n : ℕ)
    (u : HolUnif A L n) (u' : HolUnif A' L' n) (g : ℂ ≃+* ℂ) (p : A'.left ⟶ A.left),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    (∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      u.IsDiff w v → u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
    ∀ (m : Fin n → ℂ) (α : A ⟶ A) [IsMonHom α] (α' : A' ⟶ A') [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
      ((∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) ↔ (∀ w, u'.ex (fun j ↦ g (m j) * w j) = u'.ex w ≫ α')) := by
  atlas_forward_decl GlobalTheory.DiagConj.diag_endo_iff_conj_diag
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConjCMPoint

theorem conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
        ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
          (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X'),
          X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p ∧ U'.e = T.U.e ∧ U'.c = T.U.c ∧
          (∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((U'.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              U'.u.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
            (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
              ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hcm hφ c y hc 𝔠 T
  obtain ⟨X', p, hp⟩ := (GlobalTheory.RealMult.Obj.pullback_facts (F := FR E) (𝔠 := 𝔠)).1 T.X (spMap (g : ℂ →+* ℂ))
  obtain ⟨u', hlat, htan, htor⟩ := GlobalTheory.T.torsion_transport_cm_periods hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hcm hφ c y hc 𝔠 T X' p hp
  obtain ⟨u'', h', hex, ⟨χ, hah⟩, hh⟩ :=
    GlobalTheory.T.torsion_transport_cm_conjugation hPC hDR hDC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hcm hφ c y hc 𝔠 T X' p hp u' hlat htan htor
  have htan'' : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
        u''.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
    intro w v v' h1 h2
    have h3 := htan w v v' h1 h2
    unfold HolUnif.IsDiff at h3 ⊢
    rw [hex]
    exact h3
  have hB := GlobalTheory.T.period_transport_galois_conjugate T.X.A X'.A (T.X.diag T.U.c) (X'.diag T.U.c) _ T.U.u u'' g p hp.grp Ω₀ Ω₁ hT.1 hT.2.1 htan''
  let U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X' :=
    { e := T.U.e, c := T.U.c, pos := T.U.pos, u := u''
      lat := fun w ↦ by rw [← hlat w, ← u''.ker, ← u'.ker, hex]
      act := fun a w ↦ by
        haveI := T.X.rm.hom a
        haveI := X'.rm.hom a
        exact (hB (fun j ↦ φ (T.U.e j) ((a : FR E) : E)) (T.X.rm.act a) (X'.rm.act a) (hp.act a)).1 (T.U.act a) w
      h := h'
      ah := ⟨χ, hah⟩ }
  refine ⟨X', p, U', hp, rfl, rfl, hh, htan'', ?_⟩
  intro a α _ α' _ hαα' H w
  exact (hB (fun j ↦ φ (T.U.e j) a) α α' hαα').2 H w

end GlobalTheory.ConjCMPoint
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_elliptic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
        ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
          (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X'),
          X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p ∧ U'.e = T.U.e ∧ U'.c = T.U.c ∧
          (∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((U'.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              U'.u.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
            (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
              ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) := by
  atlas_forward_decl GlobalTheory.ConjCMPoint.conj_unif
end
