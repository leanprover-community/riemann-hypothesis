import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LiftsConjugateUnderStabilizer
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he in
theorem isotropic_le_orth_range : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  rw [he]
  change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  exact (D.sp.hyp_orthX a w).1

include hz in
theorem z_mem_orth_range : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  rw [hz]
  exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)

include hT he hz in

theorem exists_decomp_orth_isotropic_plus (x : (VS D).V) (hx : x ∈ orth (hS D) F0.Xplus) :
    ∃ w, x - D.sp.iXY 0 w ∈ F0.X := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hx' : x ∈ Wsp D ⊔ Xsp (lf D F0) := by rw [hW]; exact hx
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨w, by simpa using hξ⟩

include hT he hz in

theorem exists_decomp_orth_isotropic (x : (VS D).V) (hx : x ∈ orth (hS D) F0.X) :
    ∃ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X := by
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  obtain ⟨w, hw⟩ := exists_decomp_orth_isotropic_plus D u hT F0 he hz
    (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by
      rw [Formalism.MainNotions.mem_orth_iff]
      refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
      · rw [map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]
        exact hx' _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [map_sub, map_smul, F0.z_norm, smul_eq_mul]
        field_simp
        ring)
  refine ⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩
  rw [add_comm, ← sub_sub]
  exact hw

include hT he hz in

theorem Lsub_eq_of_latticeWithZ_eq (Λ₁ Λ₂ : LatV D) (h : latticeWithZ D F0 Λ₁ = latticeWithZ D F0 Λ₂) :
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) := by
  have key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔
      x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E),
        x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ := by
    intro Λ x
    have hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0) := by
      intro w c
      unfold latticeWithZ
      rw [Submodule.mem_comap]
      simp [embedWithZ]
    constructor
    · intro hx
      refine ⟨hx.2, fun w c hξ => ?_⟩
      rw [hj]
      have := (Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
    · rintro ⟨hxO, hall⟩
      obtain ⟨w, c, hξ⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x hxO
      have h1 := (hj w c).1 (hall w c hξ)
      have := (Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
  ext x
  rw [key Λ₁, key Λ₂, h]

def projWAlt : (VS D).V →ₗ[D.host.E] (D.sp.X 0).V :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm.toLinearMap ∘ₗ LinearMap.fst D.host.E _ _ ∘ₗ
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm.toLinearMap

theorem projW_apply (w : (D.sp.X 0).V) (b : (VS D).V) (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    projWAlt D (D.sp.iXY 0 w + b) = w := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold projWAlt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]

include hT he hz in

theorem exists_induced_isometry_W (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    ∃ γ ∈ isom (D.sp.X 0).hT, ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ.1
  have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
    have := hσ.2.1 D.R.rS
    rwa [partial_isotropic_top] at this
  have hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus := by
    unfold FlagG.Xplus
    rw [Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]
    congr 3
    exact hσ.2.2
  have hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus := by
    intro w
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    have : D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0) := Submodule.mem_sup_left ⟨w, rfl⟩
    rw [hW] at this
    exact this
  have hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X := by
    intro w
    refine exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_
    rw [Formalism.MainNotions.mem_orth_iff]
    intro x hx
    rw [← hXp] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    change (VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0
    rw [hσ']
    exact (Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'
  let γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0
  have hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X := by
    intro w
    obtain ⟨w', hw'⟩ := hdec w
    have e : γ0 w = w' := by
      change projWAlt D (σ (D.sp.iXY 0 w)) = w'
      have : σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w') := by abel
      rw [this]
      exact projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')
    rw [e]
    exact hw'
  have hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w' := by
    intro w w'
    have e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w)) := by abel
    have e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w')) := by abel
    have h1 := hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')
    rw [e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w))
      (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W,
      (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero] at h1
    exact h1
  have hinj : Function.Injective γ0 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  refine ⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩
  · simpa using hiso w w'
  · simpa using hγ0 w

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_latticeWithZ_iff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (Λ : LatV D) (w : (D.sp.X 0).V) (c : D.host.E) :
    (w, c) ∈ latticeWithZ D F Λ ↔ D.sp.iXY 0 w + c • F.z ∈ Lsub Λ (lf D F) := by
  unfold latticeWithZ
  rw [Submodule.mem_comap]
  simp [embedWithZ]

include he hz in
theorem extendByIdentity_mem_flag_stabilizer (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ stabF D F0 := by
  have hfix : ∀ y ∈ F0.X, (extendByIdentity D γ).symm y = y :=
    fun y hy => extendByIdentity_symm_fix_orth D γ y (isotropic_le_orth_range D u F0 he hy)
  refine ⟨extendByIdentity_mem_isom D γ hγ, fun j => ?_, ?_⟩
  · ext x
    rw [Submodule.mem_map_equiv]
    constructor
    · intro h
      have e : (extendByIdentity D γ).symm x = x := (extendByIdentity D γ).symm.injective (hfix _ (partial_isotropic_le F0 j h))
      rwa [e] at h
    · intro h
      rw [hfix x (partial_isotropic_le F0 j h)]
      exact h
  · rw [← LinearEquiv.eq_symm_apply]
    exact (extendByIdentity_symm_fix_orth D γ _ (z_mem_orth_range D u F0 hz)).symm

include he hz in

theorem transport_isLattice_latticeWithZ (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap (extendByIdentity D γ) Λ) ∧
      latticeWithZ D F0 (gmap (extendByIdentity D γ) Λ) = gmap (extendByOne D γ) (latticeWithZ D F0 Λ) := by
  have hzO := z_mem_orth_range D u F0 hz
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (isotropic_le_orth_range D u F0 he hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ hΛ
  refine ⟨hrow, ?_⟩
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLsub, isomAct_mem_gmap,
    extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem lattice_classes_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : LatticeClassesIff D u := by
  intro hTp hT3 hsp F0 he hz Λ₁ Λ₂ h₁ h₂
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨γ, hγ, ?_⟩
    have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      have := hσ.2.1 D.R.rS
      rwa [partial_isotropic_top] at this
    have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ₁
    ext ⟨w, c⟩
    have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
    have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
      have h1 := hind (γ.symm w)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
        rw [← Submodule.mem_map_equiv, hX]
        exact h1
      have hzs : σ.symm F0.z = F0.z := by
        rw [LinearEquiv.symm_apply_eq]
        exact hσ.2.2.symm
      have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
          -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
        rw [map_add, map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
        abel
      rw [e3]
      exact F0.X.neg_mem h2
    have hd' := isotropic_le_Lsub F0 Λ₁ hd
    constructor
    · intro ha
      have := (Lsub Λ₁ (lf D F0)).add_mem ha hd'
      simpa using this
    · intro hb
      have := (Lsub Λ₁ (lf D F0)).sub_mem hb hd'
      simpa using this
  · rintro ⟨γ, hγ, hγe⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ₁ h₁
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγe)
    obtain ⟨n, hn, _, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow h₂ hLs
    exact ⟨n * extendByIdentity D γ, mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ), by rw [gmap_mul, hne]⟩

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Aut

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_perpS_iff_mem_orth (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ y ∈ orth (hS D) F0.X := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rfl

theorem flag_stabilizer_map_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have := hσ.2.1 D.R.rS
  rwa [partial_isotropic_top] at this

theorem flag_stabilizer_mem_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (x : (VS D).V) (hx : x ∈ F0.X) :
    σ x ∈ F0.X := by
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ]
  exact ⟨x, hx, rfl⟩

theorem flag_stabilizer_mem_perp (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (y : (VS D).V)
    (hy : y ∈ perpS (VS D) F0.X) : σ y ∈ perpS (VS D) F0.X := by
  intro x hx
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  change (VS D).hT (σ x') (σ y) = 0
  rw [hσ.1 x' y]
  exact hy x' hx'

include he in
theorem embedding_add_smul_z_mem_perp (w : (D.sp.X 0).V) (c : D.host.E) : D.sp.iXY 0 w + c • F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 : (VS D).hT x (D.sp.iXY 0 w) = 0 :=
    Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_range D u F0 he hx) _ ⟨w, rfl⟩)
  have h2 : (VS D).hT x F0.z = 0 := Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth x hx
  rw [map_add, map_smul, h1, h2, smul_zero, add_zero]

def quotientClass (w : (D.sp.X 0).V) (c : D.host.E) : WbQ D F0 :=
  Submodule.Quotient.mk ⟨D.sp.iXY 0 w + c • F0.z, embedding_add_smul_z_mem_perp D u F0 he w c⟩

include hT hz in
theorem quotientClass_surjective (q : WbQ D F0) : ∃ w c, q = quotientClass D u F0 he w c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨w, c, h⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x.1 ((mem_perpS_iff_mem_orth D u F0 _).1 x.2)
  refine ⟨w, c, ?_⟩
  unfold quotientClass
  rw [Submodule.Quotient.eq]
  exact h

include hT hz in
theorem quotientClass_injective_left {w w' : (D.sp.X 0).V} {c c' : D.host.E} (h : quotientClass D u F0 he w c = quotientClass D u F0 he w' c') :
    w = w' := by
  unfold quotientClass at h
  rw [Submodule.Quotient.eq] at h
  have h' : D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z) ∈ F0.X := h
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hzW : ∀ v, (VS D).hT F0.z (D.sp.iXY 0 v) = 0 := fun v => by rw [hz]; exact z_orth_embedding D u v
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z)) = 0 :=
    Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth _ h')
  have hc : c = c' := by
    simp only [map_sub, map_add, map_smul, hzW, F0.z_norm, smul_eq_mul, zero_add] at h0
    have : (c - c') * ((Tu D u : ℕ) : D.host.E) = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hT'
  subst hc
  have h2 : D.sp.iXY 0 (w - w') ∈ Wsp D ⊓ Xsp (lf D F0) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    have e : D.sp.iXY 0 (w - w') = D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c • F0.z) := by
      rw [map_sub]; abel
    rw [e]
    exact h'
  rw [(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).2.1, Submodule.mem_bot] at h2
  exact sub_eq_zero.1 (embedding_W_injective D (by rw [h2, map_zero]))

def ActsAsExtendByOne (φ : WbQ D F0 → WbQ D F0) (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w c, φ (quotientClass D u F0 he w c) = quotientClass D u F0 he (γ w) c

theorem actsAsExtendByOne_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (φ : WbQ D F0 → WbQ D F0)
    (hφ : ∀ (x : perpS (VS D) F0.X) (hx : σ x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨σ x.1, hx⟩) : ActsAsExtendByOne D u F0 he φ γ := by
  intro w c
  unfold quotientClass
  rw [hφ _ (flag_stabilizer_mem_perp D u F0 σ hσ _ (embedding_add_smul_z_mem_perp D u F0 he w c)), Submodule.Quotient.eq]
  change σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) ∈ F0.X
  have e : σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) = σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) := by
    rw [map_add, map_smul, hσ.2.2]
    abel
  rw [e]
  exact hind w

theorem gmap_latticeWithZ_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (Λ : LatV D) : gmap (extendByOne D γ) (latticeWithZ D F0 Λ) = latticeWithZ D F0 (gmap σ Λ) := by
  have hX := flag_stabilizer_map_isotropic D u F0 σ hσ
  have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
  have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
    have h1 := hind (γ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
      rw [← Submodule.mem_map_equiv, hX]
      exact h1
    have hzs : σ.symm F0.z = F0.z := by
      rw [LinearEquiv.symm_apply_eq]
      exact hσ.2.2.symm
    have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
        -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
      rw [map_add, map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [e3]
    exact F0.X.neg_mem h2
  have hd' := isotropic_le_Lsub F0 Λ hd
  constructor
  · intro ha
    have := (Lsub Λ (lf D F0)).add_mem ha hd'
    simpa using this
  · intro hb
    have := (Lsub Λ (lf D F0)).sub_mem hb hd'
    simpa using this

end Aut

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u : D.what₂.Word)

theorem automorphisms_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : CardAutEqCardIsometryStabilizer D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  have hD : ∀ φ : autLz D F0 Λ,
      ∃ γ : {γ : isom (D.sp.X 0).hT // gmap (extendByOne D γ.1) (latticeWithZ D F0 Λ) = latticeWithZ D F0 Λ},
        ActsAsExtendByOne D u F0 he φ.1 γ.1.1 := by
    rintro ⟨φ, σ, hσ, hσΛ, hφ⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨⟨⟨γ, hγ⟩, ?_⟩, actsAsExtendByOne_of_induced D u F0 he σ hσ γ hind φ hφ⟩
    rw [gmap_latticeWithZ_of_induced D u F0 σ hσ γ hind Λ, hσΛ]
  choose f hf using hD
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro φ₁ φ₂ h12
    apply Subtype.ext
    funext q
    obtain ⟨w, c, rfl⟩ := quotientClass_surjective D u hT F0 he hz q
    rw [hf φ₁ w c, hf φ₂ w c, h12]
  · rintro ⟨⟨γ, hγ⟩, hγΛ⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ hΛ
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγΛ)
    obtain ⟨n, hn, hnX, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow hΛ hLs
    have hσ : n * extendByIdentity D γ ∈ stabF D F0 := mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ)
    have hσΛ : gmap (n * extendByIdentity D γ) Λ = Λ := by rw [gmap_mul, hne]
    have hind : ∀ w, (n * extendByIdentity D γ) (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
      intro w
      change n (extendByIdentity D γ (D.sp.iXY 0 w)) - _ ∈ _
      have e : extendByIdentity D γ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ w) := by
        simpa using extendByIdentity_apply D γ w 0 (Submodule.zero_mem _)
      rw [e]
      refine hnX _ ((mem_perpS_iff_mem_orth D u F0 _).1 ?_)
      simpa using embedding_add_smul_z_mem_perp D u F0 he (γ w) 0
    let φ : WbQ D F0 → WbQ D F0 := Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
      (((n * extendByIdentity D γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrict
        (fun x hx => flag_stabilizer_mem_perp D u F0 _ hσ x hx))
      (fun x hx => flag_stabilizer_mem_isotropic D u F0 _ hσ x.1 hx)
    have hφ : ∀ (x : perpS (VS D) F0.X) (hx : (n * extendByIdentity D γ) x.1 ∈ perpS (VS D) F0.X),
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(n * extendByIdentity D γ) x.1, hx⟩ := fun _ _ => rfl
    refine ⟨⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h1 := hf ⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩ w 0
    have h2 := actsAsExtendByOne_of_induced D u F0 he _ hσ γ hind φ hφ w 0
    exact quotientClass_injective_left D u hT F0 he hz (h1.symm.trans h2)

theorem gluing_mass_of_lift_transitivity (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingCount D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_iso_aut_count_genus D u hpos hlat (lattice_classes_of_lift_transitivity D u hL) (automorphisms_of_lift_transitivity D u hL) h4 h5

def GluingNumber : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ M ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    {𝓛 | (∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛) ∧ intersectFirstSummand D 𝓛 = M}.ncard = (Tu D u - 1) ^ D.R.f

theorem gluing_count_of_gluing_number (h : GluingNumber D u) : GluingCount D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ M hM
  have h1 := h hTp hT3 hsp F0 he hz Λ hΛ M hM
  refine ⟨Set.finite_of_ncard_ne_zero ?_, h1⟩
  have h2 : (Tu D u - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ (by omega)
  intro h0
  exact h2 (h1.symm.trans h0)

theorem gluing_mass_of_lift_and_number (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_lift_transitivity D u hpos hlat hL (gluing_count_of_gluing_number D u h4) h5

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Basic

variable (D : D7)

theorem orth_embedding_isometry (x y : (D.sp.X 0).V) :
    (D.sp.Y 0).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega) x y

theorem orth_embedding_injective : Function.Injective (D.sp.iXY 0) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (D.sp.X 0).nondeg.1 x fun y => ?_
  rw [← orth_embedding_isometry, hx]; simp


variable {D} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he hz in
theorem orth_embedding_mem_orth_plus (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xplus (lf D F0)) := by
  have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip (D.sp.iXY 0 x)) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      show (hS D).hT (F0.e a) (D.sp.iXY 0 x) = 0
      rw [he]
      exact c_symm0 (D.sp.hyp_orthX a x).1
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      show (hS D).hT F0.z (D.sp.iXY 0 x) = 0
      rw [hz]
      unfold D7.zmOf
      rw [map_smulₛₗ, LinearMap.smul_apply, c_symm0 (D.sp.zm_orth x), smul_zero]
  exact c_mem_orth.2 fun v hv => h hv

include he in
theorem eq_zero_of_embedding_mem_isotropic {x : (D.sp.X 0).V} (hx : D.sp.iXY 0 x ∈ Xsp (lf D F0)) : x = 0 := by
  have hx' : D.sp.iXY 0 x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by rw [← he]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx'
  have h0 : ∀ i, c i = 0 := by
    intro i
    have h1 := (D.sp.hyp_orthX i x).2
    rw [← hc, map_sum, LinearMap.sum_apply] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simpa using h1
  apply orth_embedding_injective D
  rw [← hc, map_zero]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]

include he hz in

theorem orth_space_posDef_every_place (hT : 0 < Tu D u) : Cnt.IsPosDef (D.sp.X 0).hT := by
  intro τ x hx
  have h1 := p_posX D (Tu D u) hT (lf D F0) τ (D.sp.iXY 0 x) (orth_embedding_mem_orth_plus F0 he hz x)
    (fun h => hx (eq_zero_of_embedding_mem_isotropic F0 he h))
  unfold nrm at h1
  rwa [orth_embedding_isometry] at h1

end Basic

section Lat

variable {D : D7} {T : D.host.E} (Λ : LatV D) (F : LFlag (hS D) D.R.rS T)

theorem mem_orthLattice_iff_mem_sub {x : (D.sp.X 0).V} : x ∈ L0X D Λ F ↔ D.sp.iXY 0 x ∈ L0sub Λ F := Iff.rfl

theorem orthLattice_isIntegral_of_unimodular (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F) := by
  intro x hx y hy
  obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hx).1.1
  obtain ⟨l', hl', ξ', hξ', e'⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hy).1.1
  rw [← orth_embedding_isometry, ← e, ← e']
  have h1 : (hS D).hT l ξ' = 0 := c_symm0 (c_mem_orth.1 hl.2 ξ' hξ')
  have h2 : (hS D).hT ξ l' = 0 := c_mem_orth.1 hl'.2 ξ hξ
  have h3 : (hS D).hT ξ ξ' = 0 := p_X_iso F hξ hξ'
  simp only [map_add, LinearMap.add_apply]
  rw [h1, h2, h3, add_zero, add_zero, add_zero]
  exact i_int Λ hu hl.1 hl'.1

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_one_submodule {t : E} (h : t ∈ (1 : Submodule (𝓞 E) E)) : star t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 h
  obtain ⟨o', ho'⟩ := i_star_int o
  exact Submodule.mem_one.2 ⟨o', ho'⟩

theorem mul_mem_one_submodule {s t : E} (hs : s ∈ (1 : Submodule (𝓞 E) E)) (h : t ∈ (1 : Submodule (𝓞 E) E)) :
    s * t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hs
  obtain ⟨o', rfl⟩ := Submodule.mem_one.1 h
  exact Submodule.mem_one.2 ⟨o * o', by simp⟩

end One

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)

theorem isotropic_le_orth_self : Xsp (lf D F0) ≤ orth (hS D) (Xsp (lf D F0)) :=
  fun _ hx => c_mem_orth.2 fun _ hv => p_X_iso (lf D F0) hv hx

theorem mem_Lsub_iff_sup_and_orth {v : (hS D).V} : v ∈ Lsub Λ (lf D F0) ↔
    v ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) ∧ v ∈ orth (hS D) (Xsp (lf D F0)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle : Lrep Λ (lf D F0) ⊔ toO (hS D) (Xsp (lf D F0)) ≤ Λ ⊔ toO (hS D) (Xsp (lf D F0)) :=
      sup_le_sup_right (inf_le_left : Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) ≤ Λ) _
    exact ⟨hle h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, ξ, hξ, e⟩
    have : l = v - ξ := by rw [← e]; abel
    rw [this]
    exact (orth (hS D) (Xsp (lf D F0))).sub_mem h2 (isotropic_le_orth_self F0 hξ)

include he hz in
theorem orth_embedding_mem_orth_isotropic (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xsp (lf D F0)) :=
  c_orth_anti (le_sup_left : Xsp (lf D F0) ≤ Xplus (lf D F0)) (orth_embedding_mem_orth_plus F0 he hz x)

include he hz in
theorem inner_z_orth_embedding_eq_zero (x : (D.sp.X 0).V) : (hS D).hT F0.z (D.sp.iXY 0 x) = 0 :=
  c_mem_orth.1 (orth_embedding_mem_orth_plus F0 he hz x) F0.z
    ((le_sup_right : _ ≤ Xplus (lf D F0)) (Submodule.mem_span_singleton_self _))

include he hz in

theorem mem_orthLattice_iff_image_mem_sup {x : (D.sp.X 0).V} :
    x ∈ L0X D Λ (lf D F0) ↔ D.sp.iXY 0 x ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  rw [mem_orthLattice_iff_mem_sub]
  constructor
  · intro h
    exact ((mem_Lsub_iff_sup_and_orth F0 Λ).1 h.1).1
  · intro h
    exact ⟨(mem_Lsub_iff_sup_and_orth F0 Λ).2 ⟨h, orth_embedding_mem_orth_isotropic F0 he hz x⟩, inner_z_orth_embedding_eq_zero F0 he hz x⟩

include he hz in
theorem exists_smul_mem_orthLattice (hΛ : Submodule.IsLattice D.host.E Λ) (x : (D.sp.X 0).V) :
    ∃ c : 𝓞 D.host.E, c ≠ 0 ∧ c • x ∈ L0X D Λ (lf D F0) := by
  obtain ⟨c, hc, hcx⟩ := a_exists_smul_mem Λ hΛ (D.sp.iXY 0 x)
  refine ⟨c, hc, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.mem_sup_left hcx

include he hz in

theorem orthLattice_isLattice (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) := by
  choose c hc hcM using fun i => exists_smul_mem_orthLattice F0 he hz Λ hΛ ((D.sp.X 0).frame i)
  set M₁ : Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
    Submodule.span (𝓞 D.host.E) (Set.range fun i => c i • (D.sp.X 0).frame i) with hM₁def
  have hM₁ : M₁ ≤ L0X D Λ (lf D F0) := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hcM i)
  have hfg : M₁.FG := Submodule.fg_span (Set.finite_range _)
  have hs : spanE (D.sp.X 0) M₁ = ⊤ := by
    rw [eq_top_iff, ← (D.sp.X 0).frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hc1 : algebraMap (𝓞 D.host.E) D.host.E (c i) ≠ 0 := by simpa using hc i
    have h2 : (algebraMap (𝓞 D.host.E) D.host.E (c i))⁻¹ • (c i • (D.sp.X 0).frame i) = (D.sp.X 0).frame i := by
      rw [← algebraMap_smul D.host.E (c i), smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [← h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  have hU : (⊤ : Submodule D.host.E (D.sp.X 0).V) ⊓ orth (D.sp.X 0) ⊤ = ⊥ := by
    rw [top_inf_eq, eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 y fun x => c_mem_orth.1 hy x trivial)
  obtain ⟨hdfg, -, -⟩ := g_dual_facts g_starInt hU hfg hs
  have hle : L0X D Λ (lf D F0) ≤ dualIn (D.sp.X 0) M₁ := by
    intro x hx
    refine g_mem_dualIn.2 ⟨fun y hy => ?_, by rw [hs]; trivial⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y (hM₁ hy) x hx)
    exact ⟨o, ho⟩
  refine ⟨?_, ?_⟩
  · exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian _ hdfg) _ hle
  · exact eq_top_iff.2 (hs ▸ Submodule.span_mono hM₁)

include he in

theorem mem_sup_isotropic_of_dual_pairing (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    (y : (hS D).V)
    (hy : ∀ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT m y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    y ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  have DL := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (hS D).V (hS D).hT (hS D).herm (hS D).nondeg i_star_int
  have hlat : ∀ N : LatV D, N.FG → Submodule.IsLattice D.host.E (Λ ⊔ N) := fun N hN =>
    ⟨hΛ.fg.sup hN, eq_top_iff.2 (hΛ.span_eq_top ▸ Submodule.span_mono (le_sup_left : Λ ≤ Λ ⊔ N))⟩
  have hΛ₂ := (DL _ (hlat (Submodule.span (𝓞 D.host.E) {y}) (Submodule.fg_span (Set.finite_singleton y)))).1
  choose c hc hcf using fun a => a_exists_smul_mem _ hΛ₂ (D.sp.hypF a)
  set ε : 𝓞 D.host.E := ∏ a, c a with hε
  have hε0 : ε ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hε1 : algebraMap (𝓞 D.host.E) D.host.E ε ≠ 0 := by simpa using hε0
  have hg : ∀ a, ε • D.sp.hypF a ∈
      Formalism.HermitianLatticesTheory.dual (hS D).hT (Λ ⊔ Submodule.span (𝓞 D.host.E) {y}) := by
    intro a
    rw [hε, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact Submodule.smul_mem _ _ (hcf a)
  have hgΛ : ∀ a, ε • D.sp.hypF a ∈ Λ := by
    intro a
    rw [← hu]
    exact (i_mem_dual _ _).2 fun l hl => (i_mem_dual _ _).1 (hg a) l (Submodule.mem_sup_left hl)
  have hgy : ∀ a, (hS D).hT (ε • D.sp.hypF a) y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    rw [← c_herm]
    exact star_mem_one_submodule ((i_mem_dual _ _).1 (hg a) y
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)))
  set δ : D.host.E := (star (algebraMap (𝓞 D.host.E) D.host.E ε))⁻¹ with hδ
  set N : LatV D := Submodule.span (𝓞 D.host.E) (Set.range fun a => δ • D.sp.hypE a) with hN
  have hB := (DL _ (hlat N (Submodule.fg_span (Set.finite_range _)))).2.1
  have hyB : y ∈ Λ ⊔ N := by
    rw [← hB]
    refine (i_mem_dual _ _).2 fun l hl => ?_
    have hlΛ : l ∈ Λ := by
      rw [← hu]
      exact (i_mem_dual _ _).2 fun l' hl' => (i_mem_dual _ _).1 hl l' (Submodule.mem_sup_left hl')
    have ho : ∀ a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
        (algebraMap (𝓞 D.host.E) D.host.E ε)⁻¹ * (hS D).hT (D.sp.hypE a) l := by
      intro a
      have h1 := (i_mem_dual _ _).1 hl (δ • D.sp.hypE a)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hδ, star_inv₀, star_star] at h1
      exact Submodule.mem_one.1 h1
    choose o ho using ho
    set l' : (hS D).V := ∑ a, o a • (ε • D.sp.hypF a) with hl'
    have hl'Λ : l' ∈ Λ := Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hgΛ a)
    have hm : l - l' ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) := by
      refine ⟨Λ.sub_mem hlΛ hl'Λ, ?_⟩
      show l - l' ∈ orth (hS D) (Submodule.span D.host.E (Set.range F0.e))
      rw [he]
      refine a_orth_of_frame _ _ fun b => ?_
      rw [map_sub, hl', map_sum, sub_eq_zero]
      have : ∀ a, (hS D).hT (D.sp.hypE b) (o a • (ε • D.sp.hypF a)) =
          if b = a then algebraMap (𝓞 D.host.E) D.host.E (o a) * algebraMap (𝓞 D.host.E) D.host.E ε else 0 := by
        intro a
        rw [← algebraMap_smul D.host.E (o a), ← algebraMap_smul D.host.E ε, map_smul, map_smul, D.sp.hyp_ef]
        split_ifs <;> simp
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ho b]
      field_simp
    have e : l = (l - l') + l' := by abel
    rw [e, map_add, LinearMap.add_apply]
    refine Submodule.add_mem _ (hy _ hm) ?_
    rw [hl', map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [← algebraMap_smul D.host.E (o a), map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨o a, rfl⟩)) (hgy a)
  have hNX : N ≤ toO (hS D) (Xsp (lf D F0)) := ?_
  · exact (sup_le_sup_left hNX Λ) hyB
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  show δ • D.sp.hypE a ∈ Submodule.span D.host.E (Set.range F0.e)
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)
  (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hzΛ : F0.z ∈ Λ)
  (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
  (hT : Tu D u ≠ 0)

local notation "t" => ((Tu D u : ℕ) : D.host.E)

theorem z_mem_orth_isotropic : F0.z ∈ orth (hS D) (Xsp (lf D F0)) := a_orth_of_frame F0.e F0.z F0.z_orth

include he hΛ hu hzΛ hprim hT in

theorem exists_lattice_vector_inner_z_one : ∃ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT F0.z m = 1 := by
  set M : LatV D := Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) with hM
  set I : Ideal (𝓞 D.host.E) :=
    (M.map (((hS D).hT F0.z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E) with hI
  have memI : ∀ o : 𝓞 D.host.E, o ∈ I ↔ ∃ m ∈ M, (hS D).hT F0.z m = algebraMap (𝓞 D.host.E) D.host.E o := by
    intro o
    rw [hI, Submodule.mem_comap, Submodule.mem_map]
    rfl
  have hzM : F0.z ∈ M := ⟨hzΛ, z_mem_orth_isotropic F0⟩
  have hI0 : I ≠ ⊥ := by
    intro h0
    have h1 : (-(Tu D u : 𝓞 D.host.E)) ∈ I := (memI _).2 ⟨F0.z, hzM, by rw [F0.z_norm]; simp⟩
    rw [h0, Ideal.mem_bot, neg_eq_zero] at h1
    exact hT (by exact_mod_cast h1)
  have hFI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI0
  have hinv : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ ≤ 1 := by
    intro c hc
    rw [FractionalIdeal.mem_inv_iff hFI0] at hc
    have hy : star c • F0.z ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hΛ hu _ fun m hm => ?_
      obtain ⟨i, hi⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have hiI : i ∈ I := (memI i).2 ⟨m, hm, hi.symm⟩
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hiI, rfl⟩))
      rw [map_smul, smul_eq_mul, ← c_herm F0.z m, ← star_mul', ← hi, ← ho]
      exact star_mem_one_submodule (Submodule.mem_one.2 ⟨o, rfl⟩)
    obtain ⟨o, ho⟩ := hprim (star c) ((mem_Lsub_iff_sup_and_orth F0 Λ).2
      ⟨hy, (orth (hS D) (Xsp (lf D F0))).smul_mem _ (z_mem_orth_isotropic F0)⟩)
    obtain ⟨o', ho'⟩ := i_star_int o
    refine (FractionalIdeal.mem_one_iff _).2 ⟨o', ?_⟩
    rw [ho']
    show star (o : D.host.E) = c
    rw [ho, star_star]
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = I * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ :=
          (mul_inv_cancel₀ hFI0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  obtain ⟨x, hx, hx1⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 (FractionalIdeal.one_mem_one _))
  obtain ⟨m, hm, e⟩ := (memI x).1 hx
  exact ⟨m, hm, by rw [e, hx1]⟩

include he hz hT in

theorem exists_decomp_orth_plus {v : (hS D).V} (hv : v ∈ orth (hS D) (Xsp (lf D F0))) (hvz : (hS D).hT F0.z v = 0) :
    ∃ w : (D.sp.X 0).V, ∃ ξ ∈ Xsp (lf D F0), v = D.sp.iXY 0 w + ξ := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hv' : v ∈ orth (hS D) (Xplus (lf D F0)) := by
    have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip v) := by
      refine sup_le (fun x hx => c_mem_orth.1 hv x hx) (Submodule.span_le.2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hvz
    exact c_mem_orth.2 fun x hx => h hx
  rw [← hW] at hv'
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, e⟩ := Submodule.mem_sup.1 hv'
  exact ⟨w, ξ, hξ, e.symm⟩

include he hz hT in

theorem inner_mem_one_of_mem_dual_orthLattice {m : (hS D).V} (hmΛ : m ∈ Λ) (hm : m ∈ orth (hS D) (Xsp (lf D F0)))
    (hmz : (hS D).hT F0.z m = 0) {w : (D.sp.X 0).V}
    (hw : w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0))) :
    (hS D).hT m (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, ξ, hξ, e⟩ := exists_decomp_orth_plus F0 he hz hT hm hmz
  have hx : x ∈ L0X D Λ (lf D F0) := by
    refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
    have : D.sp.iXY 0 x = m + (-ξ) := by rw [e]; abel
    rw [this]
    exact Submodule.add_mem_sup hmΛ ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ)
  rw [e, map_add, LinearMap.add_apply, orth_embedding_isometry, c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz w) ξ hξ, add_zero]
  exact (i_mem_dual _ _).1 hw x hx

include he hz hΛ hu hzΛ hprim hT in

theorem dual_orthLattice_quotient_cyclic : ∃ w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    (∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)), ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ L0X D Λ (lf D F0)) ∧
    ∀ a : 𝓞 D.host.E, a • w₁ ∈ L0X D Λ (lf D F0) ↔ ((Tu D u : ℕ) : 𝓞 D.host.E) ∣ a := by
  obtain ⟨m₁, hm₁, hzm⟩ := exists_lattice_vector_inner_z_one F0 he Λ hΛ hu hzΛ hprim hT
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set B : LatV D := Λ ⊔ toO (hS D) (Xsp (lf D F0)) with hB
  have hstar : star t = t := by simp
  have hzo := z_mem_orth_isotropic F0

  have hv1 : m₁ + t⁻¹ • F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
    (orth (hS D) (Xsp (lf D F0))).add_mem hm₁.2 ((orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo)
  have hv2 : (hS D).hT F0.z (m₁ + t⁻¹ • F0.z) = 0 := by
    rw [map_add, map_smul, hzm, F0.z_norm, smul_eq_mul]
    field_simp
    ring
  obtain ⟨w₁, ξ₁, hξ₁, e₁⟩ := exists_decomp_orth_plus F0 he hz hT hv1 hv2
  have hK1 : D.sp.iXY 0 w₁ - t⁻¹ • F0.z ∈ B := by
    have : D.sp.iXY 0 w₁ - t⁻¹ • F0.z = m₁ + (-ξ₁) := by
      have : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
      rw [this]; abel
    rw [this]
    exact Submodule.add_mem_sup hm₁.1 ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ₁)
  have hmz : (hS D).hT m₁ F0.z = 1 := by rw [← c_herm, hzm, star_one]
  have hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    refine (i_mem_dual _ _).2 fun x hx => ?_
    have e2 : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
    rw [← orth_embedding_isometry, e2, map_sub, map_add, map_smul, c_symm0 (inner_z_orth_embedding_eq_zero F0 he hz x), smul_zero, add_zero,
      c_symm0 (c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz x) ξ₁ hξ₁), sub_zero]
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 hx)
    rw [← e, map_add, LinearMap.add_apply, c_mem_orth.1 hm₁.2 ξ hξ, add_zero]
    exact i_int Λ hu hl hm₁.1
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · intro w hw

    have hα : t * (hS D).hT m₁ (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      have h1 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ Λ := Λ.add_mem (Λ.smul_mem _ hm₁.1) hzΛ
      have h2 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).add_mem
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2) hzo
      have h3 : (hS D).hT F0.z (((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z) = 0 := by
        rw [map_add, ← algebraMap_smul D.host.E, map_smul, hzm, F0.z_norm]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      rw [map_add, LinearMap.add_apply, inner_z_orth_embedding_eq_zero F0 he hz w, add_zero, ← algebraMap_smul D.host.E,
        map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h4
      have h5 : star (algebraMap (𝓞 D.host.E) D.host.E ((Tu D u : ℕ) : 𝓞 D.host.E)) = t := by
        rw [map_natCast]; exact hstar
      rwa [h5] at h4
    obtain ⟨α₀, hα₀⟩ := Submodule.mem_one.1 hα
    refine ⟨-α₀, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
    have hy : D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z ∈ B := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hΛ hu _ fun m hm => ?_
      obtain ⟨γ, hγ⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have h1 : m - γ • m₁ ∈ Λ := Λ.sub_mem hm.1 (Λ.smul_mem _ hm₁.1)
      have h2 : m - γ • m₁ ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).sub_mem hm.2
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2)
      have h3 : (hS D).hT F0.z (m - γ • m₁) = 0 := by
        rw [map_sub, ← algebraMap_smul D.host.E, map_smul, hzm, hγ]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      have h5 : (hS D).hT m (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) =
          (hS D).hT (m - γ • m₁) (D.sp.iXY 0 w) := by
        rw [map_add, map_smul, map_sub, LinearMap.sub_apply, ← algebraMap_smul D.host.E γ, map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hγ, c_herm, map_neg, hα₀]
        field_simp
        ring
      rw [h5]
      exact h4
    have e3 : D.sp.iXY 0 (w + (-α₀) • w₁) =
        (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) +
          (-α₀) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
      rw [map_add, LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E (-α₀) (t⁻¹ • F0.z), smul_smul]
      abel
    rw [e3]
    exact B.add_mem hy (B.smul_mem _ hK1)
  · intro a
    constructor
    · intro ha
      have h1 := (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 ha
      have h2 : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z ∈ B := by
        have : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z =
            D.sp.iXY 0 (a • w₁) - a • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
          rw [LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E a (t⁻¹ • F0.z), smul_smul]
          abel
        rw [this]
        exact B.sub_mem h1 (B.smul_mem _ hK1)
      obtain ⟨o, ho⟩ := hprim _ ((mem_Lsub_iff_sup_and_orth F0 Λ).2
        ⟨h2, (orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo⟩)
      refine ⟨o, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 D.host.E) D.host.E a = algebraMap (𝓞 D.host.E) D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o)
      rw [map_mul, map_natCast]
      show algebraMap (𝓞 D.host.E) D.host.E a = t * (o : D.host.E)
      rw [ho]
      field_simp
    · rintro ⟨o, rfl⟩
      refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
      have : D.sp.iXY 0 ((((Tu D u : ℕ) : 𝓞 D.host.E) * o) • w₁) =
          (((Tu D u : ℕ) : 𝓞 D.host.E) * o) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) + o • F0.z := by
        rw [LinearMap.map_smul_of_tower, smul_sub,
          ← algebraMap_smul D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o) (t⁻¹ • F0.z), smul_smul, map_mul, map_natCast,
          ← algebraMap_smul D.host.E o F0.z]
        have : (t * algebraMap (𝓞 D.host.E) D.host.E o * t⁻¹) = algebraMap (𝓞 D.host.E) D.host.E o := by
          field_simp
        rw [this]
        abel
      rw [this]
      exact B.add_mem (B.smul_mem _ hK1) (Submodule.mem_sup_left (Λ.smul_mem _ hzΛ))

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)

include hw₁ hgen in

theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha

include hw₁ hgen hann in

theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    rfl
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.LatticeGluingRadicals

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem exists_not_mem_mul_mem_span {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    ∃ c : 𝓞 E, c ∉ P ∧ ∀ x ∈ P, c * x ∈ Ideal.span {t} := by
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ht
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    have h2 : Ideal.span {t} ≤ P ^ 2 := by
      rw [hI, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span (Set.mem_singleton t))
  obtain ⟨c, hcI, hcP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨c, hcP, fun x hx => ?_⟩
  rw [hI, mul_comm c x]
  exact Ideal.mul_mem_mul hx hcI

def quotientSpanToQuotientPrime (P : Ideal (𝓞 E)) (t : 𝓞 E) (ht : t ∈ P) : (𝓞 E ⧸ Ideal.span {t}) →ₗ[𝓞 E] (𝓞 E ⧸ P) :=
  Submodule.mapQ (Ideal.span {t}) P LinearMap.id ((Ideal.span_singleton_le_iff_mem _).2 ht)

theorem isLocalizedModule_quotient_prime {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    haveI := hP.isPrime
    IsLocalizedModule P.primeCompl (quotientSpanToQuotientPrime P t ht) := by
  constructor
  · intro s
    have hs : (s : 𝓞 E) ∉ P := s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro y1 y2 h
      obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective P y1
      obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective P y2
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
      rw [← smul_sub, smul_eq_mul] at h
      exact (hP.isPrime.mem_or_mem h).resolve_left hs
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
      obtain ⟨b, i, hi, hb⟩ := hP.exists_inv hs
      refine ⟨Submodule.Quotient.mk (b * a), ?_⟩
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : (s : 𝓞 E) * (b * a) - a = -(i * a) := by linear_combination a * hb
      rw [e]
      exact P.neg_mem (P.mul_mem_right a hi)
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
    exact ⟨(Submodule.Quotient.mk a, 1), by simp [quotientSpanToQuotientPrime]⟩
  · intro x1 x2 h
    obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective _ x1
    obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    simp only [quotientSpanToQuotientPrime, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq] at h
    obtain ⟨c, hcP, hc⟩ := exists_not_mem_mul_mem_span hP ht ht2
    refine ⟨⟨c, hcP⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← smul_sub, smul_eq_mul]
    exact hc _ h

end Loc

section Idx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem localLength_cyclic_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) (hP : P.IsMaximal) (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : haveI := hP.isPrime; Formalism.HermitianLatticesTheory.locLen P A B = 1 := by
  have := hP.isPrime
  unfold Formalism.HermitianLatticesTheory.locLen
  have := isLocalizedModule_quotient_prime hP ht ht2
  have eq := IsLocalizedModule.linearEquiv P.primeCompl (i_g P A B) (quotientSpanToQuotientPrime P t ht ∘ₗ e.toLinearMap)
  rw [eq.length_eq]
  have : IsSimpleModule (𝓞 E) (𝓞 E ⧸ P) := isSimpleModule_iff_isCoatom.2 hP.out
  rw [Module.length_eq_one]
  rfl

theorem localLength_cyclic_not_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) [P.IsPrime] (ht : t ∉ P) :
    Formalism.HermitianLatticesTheory.locLen P A B = 0 := by
  have htA : ∀ x ∈ A, t • x ∈ B := by
    intro x hx
    have h1 : e (Submodule.Quotient.mk (t • (⟨x, hx⟩ : A))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self t)
    have h2 := (LinearEquiv.map_eq_zero_iff e).mp h1
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h2
    exact h2
  have hsub : Subsingleton ((Formalism.HermitianLatticesTheory.localization₂ P A) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P B).comap (Formalism.HermitianLatticesTheory.localization₂ P A).subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : ∃ s ∈ P.primeCompl, s • x ∈ A := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    show ∃ s ∈ P.primeCompl, s • x ∈ B
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mpr fun h => ?_, ?_⟩
    · rcases ‹P.IsPrime›.mem_or_mem h with h | h
      · exact ht h
      · exact Ideal.mem_primeCompl_iff.mp hs h
    · rw [mul_smul]
      exact htA _ hsx
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [Module.length_eq_zero_iff.mpr hsub]
  rfl

theorem genIdx_cyclic_split_prime {A B : Submodule (𝓞 E) S.V} (hBA : B ≤ A) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T)
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)})) :
    genIdxH A B = (T : ℝ) ^ finrank ℚ E := by
  unfold genIdxH
  have h1 : ∀ P : HeightOneSpectrum (𝓞 E),
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.lidx P.asIdeal A B) =
        ∏ᶠ (_ : P ∈ plOver E T), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    intro P
    classical
    have := P.isPrime
    rw [i_lidx_of_le P.asIdeal hBA]
    by_cases hP : P ∈ plOver E T
    · have hmax := P.isPrime.isMaximal P.ne_bot
      rw [finprod_eq_if, if_pos hP, localLength_cyclic_mem e P.asIdeal hmax hP (hs P.asIdeal hmax hP).2]
      simp
    · rw [finprod_eq_if, if_neg hP, localLength_cyclic_not_mem e P.asIdeal hP]
      simp
  rw [finprod_congr h1]
  exact finprod_plOver E hT hs id

theorem latDet_sq_of_cyclic_dual_quotient (M : Submodule (𝓞 E) S.V) (hl : Submodule.IsLattice E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual S.hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T) (w₁ : S.V)
    (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual S.hT M) (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual S.hT M, ∃ a : 𝓞 E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 E) ∣ a) :
    latDetH S.hT M = Real.sqrt ((T : ℝ) ^ finrank ℚ E) := by
  have hA : Formalism.HermitianLatticesTheory.dual S.hT M ⊓ Submodule.restrictScalars (𝓞 E) (Submodule.span E (M : Set S.V)) =
      Formalism.HermitianLatticesTheory.dual S.hT M := by
    rw [hl.span_eq_top, Submodule.restrictScalars_top, inf_top_eq]
  have hφ : ∀ a : 𝓞 E, LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩) a =
      Submodule.Quotient.mk ⟨a • w₁, (Formalism.HermitianLatticesTheory.dual S.hT M).smul_mem a hw⟩ := by
    intro a
    rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul]
    rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) := by
    intro y
    obtain ⟨⟨w, hwA⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨a, ha⟩ := hgen w hwA
    refine ⟨-a, ?_⟩
    rw [hφ, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, Submodule.subtype_apply,
      Submodule.subtype_apply]
    have h1 : -a • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [h1]
    exact M.neg_mem ha
  have hK : LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) =
      Ideal.span {((T : ℕ) : 𝓞 E)} := by
    ext a
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Ideal.mem_span_singleton]
    exact hker a
  unfold latDetH dualInH
  rw [hA]
  congr 1
  exact genIdx_cyclic_split_prime hint hT hs
    ((Submodule.quotEquivOfEq _ _ hK).symm.trans (LinearMap.quotKerEquivOfSurjective _ hsurj)).symm

end Idx

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_rat_E_eq_two_f (D : D7) : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)
  ring

theorem latDet_of_cyclic_dual_quotient (D : D7) (M : Submodule (𝓞 D.host.E) (D.sp.X 0).V) (hl : Submodule.IsLattice D.host.E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl D.host.E T)
    (w₁ : (D.sp.X 0).V) (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M)
    (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a) :
    latDetH (D.sp.X 0).hT M = ((T ^ D.R.f : ℕ) : ℝ) := by
  rw [latDet_sq_of_cyclic_dual_quotient M hl hint hT hs w₁ hw hgen hker, finrank_rat_E_eq_two_f, pow_mul',
    Real.sqrt_sq (by positivity)]
  norm_cast

end Record

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gluing_mass_of_lift_number_genus (D : D7) (u : D.what₂.Word) (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u := by
  intro hT
  exact gluing_mass_of_lift_and_number D u (orth_space_posDef D u hT.pos)
    (fun hT h3 hsp F0 he hz Λ hΛ => (orthLattice_structure D u hT h3 hsp F0 he hz Λ hΛ).1) hL h4 h5 hT

end Formalism.MainNotions.BridgeLemma₂

end
end
