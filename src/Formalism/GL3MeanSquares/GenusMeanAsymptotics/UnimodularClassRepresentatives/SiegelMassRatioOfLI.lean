import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassConstSucc
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoMeanAlphaN
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsTotPosDefOfSmul

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def starFixed (K : Type) [Field K] [CharZero K] [StarRing K] : IntermediateField ℚ K where
  carrier := {a : K | star a = a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  algebraMap_mem' := by
    intro q
    exact map_ratCast (starRingEnd K) q
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [star_inv₀, ha]

theorem exists_fixF (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F K), IsFixF K F := by
  haveI : FiniteDimensional ℚ (starFixed K) := IntermediateField.finiteDimensional_left (starFixed K)
  haveI : NumberField (starFixed K) := ⟨⟩
  refine ⟨starFixed K, inferInstance, inferInstance, inferInstance, fun a => ?_⟩
  constructor
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact b.2

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

theorem exists_reps {X : Type*} (r : X → X → Prop) (hr : Equivalence r) (A X₀ : Set X)
    (hfin : X₀.Finite) (hcov : ∀ x ∈ A, ∃ t ∈ X₀, r t x) :
    ∃ R : Finset X, (∀ t ∈ R, t ∈ X₀) ∧ ∀ x ∈ A, ∃! t, t ∈ R ∧ r t x := by
  classical
  let s : Setoid X := ⟨r, hr⟩
  let pick : Quotient s → X := fun c =>
    if H : ∃ t ∈ X₀, Quotient.mk s t = c then H.choose else Quotient.out c
  have hp1 : ∀ x ∈ X₀, pick (Quotient.mk s x) ∈ X₀ ∧
      Quotient.mk s (pick (Quotient.mk s x)) = Quotient.mk s x := by
    intro x hx
    have H : ∃ t ∈ X₀, Quotient.mk s t = Quotient.mk s x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos H]
    exact H.choose_spec
  refine ⟨hfin.toFinset.image (fun x => pick (Quotient.mk s x)), ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact (hp1 x (hfin.mem_toFinset.mp hx)).1
  · intro x hx
    obtain ⟨t₀, ht₀, h0⟩ := hcov x hx
    refine ⟨pick (Quotient.mk s t₀),
      ⟨Finset.mem_image.mpr ⟨t₀, hfin.mem_toFinset.mpr ht₀, rfl⟩, ?_⟩, ?_⟩
    · exact hr.trans (Quotient.exact (hp1 t₀ ht₀).2) h0
    · rintro t' ⟨ht', h1⟩
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp ht'
      have e1 := (hp1 x' (hfin.mem_toFinset.mp hx')).2
      have e2 : Quotient.mk s x' = Quotient.mk s t₀ := by
        rw [← e1]
        exact Quotient.sound (hr.trans h1 (hr.symm h0))
      rw [e2]

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

@[reducible] def actV (S : VecSplit h h') : MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V) where
  smul g M := Formalism.HermitianLatticesTheory.gmap (extHom S g.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S 1) M = M
    rw [map_one]
    exact autSub_gmap_one M
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S (a.1 * b.1)) M = _
    rw [map_mul]
    exact autSub_gmap_mul _ _ _

@[reducible] def actV' (h' : V' →ₗ⋆[K] V' →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V') where
  smul g T := Formalism.HermitianLatticesTheory.gmap g.1 T
  one_smul T := autSub_gmap_one T
  mul_smul _ _ _ := autSub_gmap_mul _ _ _

theorem stab_actV (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    @MulAction.stabilizer _ _ _ (actV S) M = (autExt S M).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro e
    exact ⟨SplitBAux.extOf_mem_isom hs S g.2, e⟩
  · intro e
    exact e.2

theorem stab_actV' (T : Submodule (𝓞 K) V') :
    @MulAction.stabilizer _ _ _ (actV' h') T = (autSub h' T).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by
  ext g
  rw [Subgroup.mem_subgroupOf]
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

theorem autSub_le_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) :
    autSub h A ≤ Formalism.HermitianLatticesTheory.isom h := fun _ hg => hg.1

theorem relIndex_stab (hs : h.IsSymm) (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    (@MulAction.stabilizer _ _ _ (actV S) M).relIndex
      (@MulAction.stabilizer _ _ _ (actV' h') (S.cut M)) = oM S M := by
  rw [stab_actV hs, stab_actV', Subgroup.relIndex_subgroupOf (autSub_le_isom h' _)]
  rfl

theorem extOf_res (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : SplitBAux.extOf S (SplitBAux.res S g hg hx) = g := by
  apply LinearEquiv.toLinearMap_injective
  apply SplitBAux.linearMap_ext S
  · change SplitBAux.extOf S _ S.x₀ = g S.x₀
    rw [SplitBAux.extOf_x₀, hx]
  · intro a
    change SplitBAux.extOf S _ (S.ι a) = g (S.ι a)
    rw [SplitBAux.extOf_ι, SplitBAux.res_spec]

theorem gmap_smul (g : V ≃ₗ[K] V) (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (I • A) = I • Formalism.HermitianLatticesTheory.gmap g A := Submodule.map_smul'' _ _ _

theorem conj_mem_autSub {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h A) : g * u * g⁻¹ ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨mul_mem (mul_mem hg hu.1) (inv_mem hg), ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, ← autSub_gmap_mul g⁻¹ g, inv_mul_cancel, autSub_gmap_one, hu.2]

theorem conj_mem_autSub' {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A)) : g⁻¹ * u * g ∈ autSub h A := by
  refine ⟨mul_mem (mul_mem (inv_mem hg) hu.1) hg, ?_⟩
  rw [autSub_gmap_mul, autSub_gmap_mul, hu.2, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem mem_tube_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x y : V) :
    g y ∈ tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x ↔
      y ∈ tube (autSub h A) A 𝔭 J (g.symm x) := by
  constructor
  · rintro ⟨u, hu, hm⟩
    refine ⟨g⁻¹ * u * g, conj_mem_autSub' hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, map_sub, g.symm_apply_apply] at hm
    change y - g.symm (u (g (g.symm x))) ∈ _
    rwa [g.apply_symm_apply]
  · rintro ⟨u, hu, hm⟩
    refine ⟨g * u * g⁻¹, conj_mem_autSub hg hu, ?_⟩
    rw [← gmap_smul, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
    change g.symm (g y - g (u (g.symm x))) ∈ _
    rwa [← map_sub, g.symm_apply_apply]

theorem image_tube {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (A : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    g '' tube (autSub h A) A 𝔭 J (g.symm x) =
      tube (autSub h (Formalism.HermitianLatticesTheory.gmap g A)) (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 J x := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_tube_gmap hg A 𝔭 J x y).2 hy
  · intro hz
    refine ⟨g.symm z, (mem_tube_gmap hg A 𝔭 J x _).1 ?_, g.apply_symm_apply z⟩
    rwa [g.apply_symm_apply]

theorem cut_props (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      IsIntegralAt 𝔭 h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ∧
      fibLoc S L 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) ≠ 0 := by
  rw [LocalizedFibreSets.gmap_locF] at hx ⊢
  rw [LocalizedFibreSets.cut_locF]
  refine ⟨LocalizedFibreSets.locF_idem _ _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF
    (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)), ?_⟩
  rw [UnimodularLocalization.fibLoc_locF]
  obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
  have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro e
    have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
    have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
    exact ht (e2 ▸ 𝔭.zero_mem)
  have hgood := BrB.good_cut (F := F) hK hF hs hd (BrB.scaleSplit S _ hc)
    (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi)
    (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
        rw [algebraMap_smul]; exact hx)
  have h1 := hgood.2 ⟨𝔭, h𝔭⟩
  rw [BrB.fibLoc_scale S L h𝔭.isPrime hg ht hc] at h1
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem extOf_one (S : VecSplit h h') : SplitBAux.extOf S 1 = 1 := by
  rw [← extHom_apply, map_one]

theorem extOf_mul (S : VecSplit h h') (a b : V' ≃ₗ[K] V') :
    SplitBAux.extOf S (a * b) = SplitBAux.extOf S a * SplitBAux.extOf S b := by
  rw [← extHom_apply, ← extHom_apply, ← extHom_apply, map_mul]

theorem gmap_extOf_inv (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, mul_inv_cancel, extOf_one, autSub_gmap_one]

theorem gmap_extOf_inv' (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) M) = M := by
  rw [← autSub_gmap_mul, ← extOf_mul, inv_mul_cancel, extOf_one, autSub_gmap_one]

theorem orb_equiv (S : VecSplit h h') :
    Equivalence (fun M₁ M₂ : Submodule (𝓞 K) V =>
      ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M₁ = M₂) := by
  refine ⟨fun M => ⟨1, one_mem _, by rw [extOf_one, autSub_gmap_one]⟩, ?_, ?_⟩
  · rintro M₁ M₂ ⟨g', hg', e⟩
    exact ⟨g'⁻¹, inv_mem hg', by rw [← e, gmap_extOf_inv']⟩
  · rintro M₁ M₂ M₃ ⟨g', hg', e⟩ ⟨g'', hg'', e'⟩
    exact ⟨g'' * g', mul_mem hg'' hg', by rw [extOf_mul, autSub_gmap_mul, e, e']⟩

theorem through_smul (hs : h.IsSymm) (S : VecSplit h h') {A M : Submodule (𝓞 K) V}
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (hM : (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = M) ∧ S.x₀ ∈ M) :
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M) ∧
      S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M := by
  obtain ⟨⟨g, hg, hgA⟩, hxM⟩ := hM
  refine ⟨⟨SplitBAux.extOf S g' * g, mul_mem (SplitBAux.extOf_mem_isom hs S hg') hg, ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, hgA]
  · exact ⟨S.x₀, hxM, SplitBAux.extOf_x₀ S g'⟩

theorem tube_add (D : Subgroup (V ≃ₗ[K] V)) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) {J k : ℕ}
    (hJk : J ≤ k) (x : V) {y z : V} (hy : y ∈ tube D A 𝔭 J x)
    (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) : y + z ∈ tube D A 𝔭 J x := by
  obtain ⟨g, hg, hy'⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hz' : z ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hJk) hz
  have e : y + z - g x = (y - g x) + z := by abel
  rw [e]
  exact add_mem hy' hz'

theorem autSub_apply_mem {u : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hu : u ∈ autSub h A) {x : V}
    (hx : x ∈ A) : u x ∈ A := by
  have h2 : Formalism.HermitianLatticesTheory.gmap u A = A := hu.2
  rw [← h2]
  exact ⟨x, hx, rfl⟩

theorem same_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Formalism.HermitianLatticesTheory.isom h) (hg₂ : g₂ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx₁ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) (hx₂ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1 ≤ J) {y : V}
    (h1 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₁.symm S.x₀))
    (h2 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₂.symm S.x₀)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) =
      Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L) := by
  have hx₁' : g₁.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₁ (locF 𝔭 L) S.x₀).1 hx₁
  have hx₂' : g₂.symm S.x₀ ∈ locF 𝔭 L := (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g₂ (locF 𝔭 L) S.x₀).1 hx₂
  obtain ⟨u₁, hu₁, hy₁⟩ := h1
  obtain ⟨u₂, hu₂, hy₂⟩ := h2
  have ha : u₁ (g₁.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₁ hx₁'
  have hb : u₂ (g₂.symm S.x₀) ∈ locF 𝔭 L := autSub_apply_mem hu₂ hx₂'
  have hna : h (u₁ (g₁.symm S.x₀)) (u₁ (g₁.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₁.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₁), hx]
  have hnb : h (u₂ (g₂.symm S.x₀)) (u₂ (g₂.symm S.x₀)) = algebraMap F K (n : F) := by
    rw [SplitBAux.isom_apply hu₂.1, SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg₂), hx]
  have hxy : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) ∈
      ((extP K 𝔭) ^ J • (locF 𝔭 L) : Submodule (𝓞 K) V) := by
    have e : u₂ (g₂.symm S.x₀) - u₁ (g₁.symm S.x₀) =
        (y - u₁ (g₁.symm S.x₀)) - (y - u₂ (g₂.symm S.x₀)) := by abel
    rw [e]
    exact sub_mem hy₁ hy₂
  obtain ⟨w, hw, -, hwab⟩ := exists_isom_congr hK hF hs hd hL hLi h𝔭 hn ha hb hna hnb hJ hxy
  set G : V ≃ₗ[K] V := g₂ * u₂⁻¹ * w * u₁ * g₁⁻¹ with hGdef
  have hG : G ∈ Formalism.HermitianLatticesTheory.isom h :=
    mul_mem (mul_mem (mul_mem (mul_mem hg₂ (inv_mem hu₂.1)) hw.1) hu₁.1) (inv_mem hg₁)
  have hGx : G S.x₀ = S.x₀ := by
    change g₂ (u₂.symm (w (u₁ (g₁.symm S.x₀)))) = S.x₀
    rw [hwab, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  refine ⟨SplitBAux.res S G hG hGx, SplitBAux.res_mem_isom S G hG hGx, ?_⟩
  rw [extOf_res, ← autSub_gmap_mul]
  have e : G * g₁ = g₂ * u₂⁻¹ * w * u₁ := by
    rw [hGdef, inv_mul_cancel_right]
  rw [e, autSub_gmap_mul, hu₁.2, autSub_gmap_mul, hw.2, autSub_gmap_mul, (inv_mem hu₂).2]

theorem exists_on_orbit (hs : h.IsSymm) (S : VecSplit h h') {A : Submodule (𝓞 K) V}
    {g γ : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h')
    (e : Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap γ A) = Formalism.HermitianLatticesTheory.gmap g A) {y : V}
    (hy : g y = S.x₀) : ∃ u ∈ autSub h A, u (γ.symm S.x₀) = y := by
  refine ⟨g⁻¹ * SplitBAux.extOf S g' * γ, ?_, ?_⟩
  · show _ ∈ Formalism.HermitianLatticesTheory.isom h ∧ _
    refine ⟨mul_mem (mul_mem (inv_mem hg) (SplitBAux.extOf_mem_isom hs S hg')) hγ, ?_⟩
    rw [autSub_gmap_mul, autSub_gmap_mul, e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, SplitBAux.extOf_x₀,
      ← hy]
    exact g.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def MSet (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    Set (Submodule (𝓞 K) V) :=
  {M | (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = M) ∧ S.x₀ ∈ M}

def IsMReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (s : Finset (Submodule (𝓞 K) V')) (R : Finset (Submodule (𝓞 K) V)) : Prop :=
  (∀ M ∈ R, M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s) ∧
  ∀ M ∈ MSet S L 𝔭, ∃! M₀, M₀ ∈ R ∧
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M₀ = M

theorem mem_fib_iff (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {T : Submodule (𝓞 K) V'} (hT : locF 𝔭 T = T) (Λ : Submodule (𝓞 K) V) :
    (locF 𝔭 Λ = Λ ∧ (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
      S.cut Λ = locF 𝔭 T) ↔ (Λ ∈ MSet S L 𝔭 ∧ S.cut Λ = T) := by
  constructor
  · rintro ⟨_, hg, hx, hc⟩
    exact ⟨⟨hg, hx⟩, hc.trans hT⟩
  · rintro ⟨⟨⟨g, hg, hgL⟩, hx⟩, hc⟩
    refine ⟨?_, ⟨g, hg, hgL⟩, hx, hc.trans hT.symm⟩
    rw [← hgL, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.locF_idem]

theorem card_fib (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {T : Submodule (𝓞 K) V'} (hT : locF 𝔭 T = T) :
    Nat.card {Λ // Λ ∈ MSet S L 𝔭 ∧ S.cut Λ = T} = fibLoc S L 𝔭 T := by
  unfold fibLoc
  exact Nat.card_congr (Equiv.subtypeEquivRight fun Λ => (mem_fib_iff S L 𝔭 hT Λ).symm)

theorem exists_mReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) : ∃ R, IsMReps S L 𝔭 s R := by
  have hfin : {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s}.Finite := by
    have hsub : {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s} ⊆
        ⋃ T ∈ s, {M | M ∈ MSet S L 𝔭 ∧ S.cut M = T} := by
      rintro M ⟨h1, h2⟩
      exact Set.mem_biUnion h2 ⟨h1, rfl⟩
    refine (Set.Finite.biUnion s.finite_toSet fun T hT => ?_).subset hsub
    obtain ⟨hT1, -, hT3⟩ := hsr.1 T hT
    rw [← card_fib S L 𝔭 hT1] at hT3
    exact Nat.finite_of_card_ne_zero hT3
  have hcov : ∀ M ∈ MSet S L 𝔭, ∃ t ∈ {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s},
      ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') t = M := by
    intro M hM
    obtain ⟨⟨g, hg, rfl⟩, hxM⟩ := hM
    obtain ⟨a, b, c⟩ := OrbF.cut_props hK hF hs hd S hL hLi h𝔭 hg hxM
    obtain ⟨T₀, ⟨hT₀, g', hg', e⟩, -⟩ := hsr.2 _ a b c
    refine ⟨Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g'⁻¹) (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)),
      ⟨OrbF.through_smul hs S (inv_mem hg') ⟨⟨g, hg, rfl⟩, hxM⟩, ?_⟩, g', hg',
      OrbF.gmap_extOf_inv S g' _⟩
    rw [StabilizerLattices.cut_gmap_extOf, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
    exact hT₀
  exact OrbF.exists_reps _ (OrbF.orb_equiv S) (MSet S L 𝔭) _ hfin hcov

theorem nkCount_eq_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {s : Finset (Submodule (𝓞 K) V')} {R : Finset (Submodule (𝓞 K) V)} (hR : IsMReps S L 𝔭 s R) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      nkCount h L 𝔭 k n = ∑ M ∈ R, cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) := by
  classical
  have hch : ∀ M : Submodule (𝓞 K) V, ∃ g : V ≃ₗ[K] V,
      M ∈ R → g ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = M := by
    intro M
    by_cases hM : M ∈ R
    · obtain ⟨⟨⟨g, hg, e⟩, -⟩, -⟩ := hR.1 M hM
      exact ⟨g, fun _ => ⟨hg, e⟩⟩
    · exact ⟨1, fun hM' => absurd hM' hM⟩
  choose γ hγ using hch
  obtain ⟨c₀, hc₀⟩ := exists_exact_near hK hF hs hd hL hLi h𝔭 hn ⟨S.x₀, hx⟩
  filter_upwards [eventually_ge_atTop (4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1)] with J hJ
  filter_upwards [eventually_ge_atTop (c₀ + J)] with k hk
  have hterm : ∀ M ∈ R, cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) =
      cnt h (locF 𝔭 L) 𝔭 k n
        (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀)) := by
    intro M hM
    obtain ⟨hg, e⟩ := hγ M hM
    have h1 := cnt_gmap hg (locF 𝔭 L) 𝔭 k n
      (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀))
    rw [OrbF.image_tube hg, e] at h1
    exact h1
  have hst : ∀ M ∈ R, ∀ y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀),
      ∀ z ∈ ((extP K 𝔭) ^ k • locF 𝔭 L : Submodule (𝓞 K) V),
      y + z ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀) :=
    fun M _ y hy z hz => OrbF.tube_add _ _ 𝔭 (by omega) _ hy hz
  have hdis : ∀ M ∈ R, ∀ M' ∈ R, M ≠ M' →
      Disjoint (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀))
        (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M').symm S.x₀)) := by
    intro M hM M' hM' hne
    rw [Set.disjoint_left]
    intro y h1 h2
    obtain ⟨hg, e⟩ := hγ M hM
    obtain ⟨hg', e'⟩ := hγ M' hM'
    have hxM := (hR.1 M hM).1.2
    have hxM' := (hR.1 M' hM').1.2
    obtain ⟨g', hg'', e''⟩ := OrbF.same_orbit hK hF hs hd S hL hLi h𝔭 hn hx hg hg'
      (by rw [e]; exact hxM) (by rw [e']; exact hxM') hJ h1 h2
    rw [e, e'] at e''
    exact hne ((hR.2 M' (hR.1 M' hM').1).unique ⟨hM, g', hg'', e''⟩
      ⟨hM', 1, one_mem _, by rw [OrbF.extOf_one, autSub_gmap_one]⟩)
  rw [Finset.sum_congr rfl hterm, ← cnt_biUnion h (locF 𝔭 L) 𝔭 k n (finite_quot hL h𝔭 k) R _ hst hdis,
    ← nkCount_locF hF h L 𝔭 h𝔭 k n]
  symm
  apply cnt_eq_nkCount
  intro y hy hyn
  obtain ⟨y', hy', hn', hclose⟩ := hc₀ k (by omega) y hy hyn
  have hy0 : y' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn'
    exact S.hx₀ (hx.trans hn'.symm)
  obtain ⟨g, hg, hgy⟩ := exists_isom_map_of_eq hK hs hd hy0 (hn'.trans hx.symm)
  have hMS : Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) ∈ MSet S L 𝔭 := ⟨⟨g, hg, rfl⟩, ⟨y', hy', hgy⟩⟩
  obtain ⟨M₀, ⟨hM₀, g', hg', e⟩, -⟩ := hR.2 _ hMS
  obtain ⟨hγ₀, e₀⟩ := hγ M₀ hM₀
  rw [← e₀] at e
  obtain ⟨u, hu, hu'⟩ := OrbF.exists_on_orbit hs S hg hγ₀ hg' e hgy
  refine Set.mem_biUnion hM₀ ⟨u, hu, ?_⟩
  rw [hu', ← neg_sub]
  exact neg_mem (pow_smul_anti 𝔭 _ (by omega) hclose)

theorem sum_oM (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    {R : Finset (Submodule (𝓞 K) V)} (hR : IsMReps S L 𝔭 s R)
    (w : Submodule (𝓞 K) V' → ℝ) :
    ∑ M ∈ R, (oM S M : ℝ) * w (S.cut M) = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * w T := by
  have key := @sum_relIndex_fibre (Formalism.HermitianLatticesTheory.isom h') _ _ _ (OrbF.actV S) (OrbF.actV' h') S.cut
    (fun g M => StabilizerLattices.cut_gmap_extOf S g.1 M) (MSet S L 𝔭)
    (fun g M hM => OrbF.through_smul hs S g.2 hM) R s hR.1
    (fun M hM => by
      obtain ⟨t, ⟨ht, g', hg', e⟩, huniq⟩ := hR.2 M hM
      exact ⟨t, ⟨ht, ⟨g', hg'⟩, e⟩, fun t' ht' => huniq t' ⟨ht'.1, ht'.2.choose.1, ht'.2.choose.2,
        ht'.2.choose_spec⟩⟩)
    (fun y hy y' hy' hg => by
      obtain ⟨g, e⟩ := hg
      obtain ⟨a, b, c⟩ := hsr.1 y' hy'
      exact (hsr.2 y' a b c).unique ⟨hy, g.1, g.2, e⟩ ⟨hy', 1, one_mem _, autSub_gmap_one _⟩)
    (fun M hM => by
      rw [OrbF.relIndex_stab hs]
      obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
      rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
      exact oM_ne_zero hs S (LocalizedFibreSets.isLattice_gmap g hL) h𝔭 hxM) w
  calc ∑ M ∈ R, (oM S M : ℝ) * w (S.cut M) = _ :=
        Finset.sum_congr rfl fun M _ => by rw [← OrbF.relIndex_stab hs]
    _ = _ := key
    _ = _ := Finset.sum_congr rfl fun T hT => by rw [card_fib S L 𝔭 (hsr.1 T hT).1]

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nu_gmap_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    nu h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = nu h L 𝔭 ∧
      vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
  have hv : vd h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = vd h L 𝔭 := by
    rw [UnimodularLocalization.vd_gmap hg, vd_locF hK hF hs hd hL hLi h𝔭]
  have ha : alphaL h (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) 𝔭 = alphaL h L 𝔭 := by
    rw [BrB.alphaL_gmap hg]
    unfold alphaL
    simp only [akCount_locF hF h L 𝔭 h𝔭]
  refine ⟨?_, hv⟩
  unfold nu
  rw [ha, hv]

theorem main_term (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₂ : Submodule (𝓞 K) V} (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂)
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      (nkCount h L 𝔭 k n : ℝ) = kap S (locF 𝔭 M₂) 𝔭 n J k *
        ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) *
        ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * (nu h' T 𝔭)⁻¹ := by
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr
  have h1 := nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR
  have h2 : ∀ M ∈ R, ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact kap_eq hK hF hs hd S (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi) hM₂ hM₂i
      h𝔭 hn hx hxM hx₂
  have h3 : ∀ᶠ J in atTop, ∀ᶠ k in atTop, ∀ M ∈ R,
      kap S M 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
    filter_upwards [(Finset.eventually_all R).mpr h2] with J hJ
    exact (Finset.eventually_all R).mpr hJ
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  filter_upwards [h1, h3] with J hJ1 hJ3
  filter_upwards [hJ1, hJ3] with k hk1 hk3
  rw [hk1, ← sum_oM hK hF hs hd S hL hLi h𝔭 hsr hR (fun T => (nu h' T 𝔭)⁻¹), Nat.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [← hk3 M hM]
  obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
  obtain ⟨e1, e2⟩ := nu_gmap_locF hK hF hs hd hL hLi h𝔭 hg
  have hν : 0 < nu h L 𝔭 := by
    rw [← e1, LocalizedFibreSets.gmap_locF]
    exact nu_pos hK hF hs hd (LocalizedFibreSets.isLattice_gmap g hL) (UnimodularLocalization.isIntegralLat_gmap hg hLi) h𝔭
  have hν' : 0 < nu h' (S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))) 𝔭 := by
    rw [LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
    exact nu_pos hK hF (S.isSymm hs) (S.isTotPosDef hd)
      (StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL))
      (UnimodularLocalization.isIntegralLat_cut S (UnimodularLocalization.isIntegralLat_gmap hg hLi)) h𝔭
  have ho : (oM S (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : ℝ) ≠ 0 := by
    rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
    exact_mod_cast oM_ne_zero hs S (LocalizedFibreSets.isLattice_gmap g hL) h𝔭 hxM
  unfold kap
  rw [e1, e2]
  have hq' := pow_pos hq (vd h L 𝔭)
  field_simp

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem eigenvalue_eq₂ (T : Submodule (𝓞 K) V') (𝔭 : Ideal (𝓞 F)) :
    lamP h' T 𝔭 = alphaStd K 𝔭 (finrank K V') * (nu h' T 𝔭)⁻¹ := by
  unfold lamP nu
  rw [inv_div, mul_div_assoc]

theorem repRatio_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) {κ σ : ℝ}
    (e : (nkCount h L 𝔭 k n : ℝ) = κ * ((Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 * nu h L 𝔭) * σ) :
    repRatio h L 𝔭 n = κ / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) * σ := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hα := alphaL_pos hK hF hs hd hL hLi h𝔭
  unfold repRatio
  rw [alphaN_eq_of_le hK hF hs hd hL hLi h𝔭 hn hk, e]
  unfold nu
  have e2 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * (Ideal.absNorm 𝔭 : ℝ) ^ vd h L 𝔭 := by
    rw [← pow_add, ← S.finrank_add_one, Nat.add_sub_cancel, Nat.succ_mul]
  rw [e2]
  have h1 := pow_pos hq ((finrank K V - 1) * vd h L 𝔭)
  have h2 := pow_pos hq (vd h L 𝔭)
  have h3 := pow_pos hq (k * (2 * finrank K V - 1))
  field_simp

theorem repRatio_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hE : ¬ ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsLattice K M₂ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧
      S.x₀ ∈ locF 𝔭 M₂) : repRatio h L 𝔭 n = 0 := by
  obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
  obtain ⟨R, hR⟩ := exists_mReps hK hF hs hd S hL hLi h𝔭 hn hx hsr
  have hR0 : R = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
    rw [LocalizedFibreSets.gmap_locF] at hxM
    exact hE ⟨_, LocalizedFibreSets.isLattice_gmap g hL, UnimodularLocalization.isIntegralLat_gmap hg hLi, hxM⟩
  obtain ⟨J, hJ⟩ := (nkCount_eq_sum hK hF hs hd S hL hLi h𝔭 hn hx hR).exists
  obtain ⟨k, hk1, hk2⟩ := (hJ.and (eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2))).exists
  rw [hR0, Finset.sum_empty] at hk1
  rw [repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk2 (κ := 0) (σ := 0) (by rw [hk1]; simp)]
  simp

end LIOrb

open LIOrb in
theorem liRatio : LIRatio := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  by_cases hE : ∃ M₂ : Submodule (𝓞 K) V, Submodule.IsLattice K M₂ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat h M₂ ∧ S.x₀ ∈ locF 𝔭 M₂
  · obtain ⟨M₂, hM₂, hM₂i, hx₂⟩ := hE
    obtain ⟨s, hsr⟩ := exists_locReps hK hF hs hd S hL hLi h𝔭
    obtain ⟨s₀, hsr₀⟩ := exists_locReps hK hF hs hd S hL₀ hL₀i h𝔭
    obtain ⟨J, hJ, hJ₀⟩ := ((main_term hK hF hs hd S hL hLi hM₂ hM₂i h𝔭 hn hx hx₂ hsr).and
      (main_term hK hF hs hd S hL₀ hL₀i hM₂ hM₂i h𝔭 hn hx hx₂ hsr₀)).exists
    obtain ⟨k, ⟨hk, hk₀⟩, hk1, hk2⟩ := ((hJ.and hJ₀).and
      ((eventually_ge_atTop (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2)).and
        (eventually_ge_atTop (2 * vd h L₀ 𝔭 + 2 * vF 𝔭 n + 2)))).exists
    rw [psiP_eq_sum hK hF hs hd S hL hLi h𝔭 hsr, psiP_eq_sum hK hF hs hd S hL₀ hL₀i h𝔭 hsr₀,
      repRatio_eq hK hF hs hd S hL hLi h𝔭 hn hk1 hk, repRatio_eq hK hF hs hd S hL₀ hL₀i h𝔭 hn hk2 hk₀]
    simp only [eigenvalue_eq₂, mul_left_comm _ (alphaStd K 𝔭 (finrank K V')), ← Finset.mul_sum]
    ring
  · rw [repRatio_eq_zero hK hF hs hd S hL hLi h𝔭 hn hx hE,
      repRatio_eq_zero hK hF hs hd S hL₀ hL₀i h𝔭 hn hx hE, mul_zero, mul_zero]

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace PinD

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero (algebraMap F K)).2 hnF
  set S₁ := unscale hc S with hS₁
  have hx1 : h S₁.x₀ S₁.x₀ = 1 := by
    have e := hx
    rw [smul_form_apply] at e
    exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
  have hs : h.IsSymm := isSymm_of_smul hF hc hs'
  have hd : IsTotPosDef h := isTotPosDef_of_smul hK hF hs hd' hx1
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 := fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hx1' : h S₁.x₀ S₁.x₀ = algebraMap F K ((1 : 𝓞 F) : F) := by
    rw [hx1]
    simp
  obtain ⟨L₀, hL, hLi, hxL, hvd⟩ := exists_lattice_vd_le_one hK hF hs hd h𝔭 hx1' h1𝔭
  have hs₁' : h'.IsSymm := S₁.isSymm hs
  have hd₁' : IsTotPosDef h' := S₁.isTotPosDef hd
  have hsc' := S.isSymm hs'
  have hdc' := S.isTotPosDef hd'
  have hadj : S₁.adjoin (S₁.cut L₀) = L₀ := S₁.adjoin_cut hx1 hLi hxL
  have hC : Submodule.IsLattice K (S₁.cut L₀) := by
    rw [← S₁.isLattice_adjoin_iff, hadj]
    exact hL
  have hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S₁.cut L₀) := Formalism.HermitianLattices.Ext.L3.UnimodularLocalization.isIntegralLat_cut S₁ hLi
  have hvdC : vd h' (S₁.cut L₀) 𝔭 = vd h L₀ 𝔭 := PinC.vd_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭
  have hm := S₁.finrank_add_one
  have hLic := PinA.isIntegralLat_smul hLi n
  have hCic := PinA.isIntegralLat_smul hCi n
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hsplit : alphaL h L₀ 𝔭 = alphaN h L₀ 𝔭 1 * alphaL h' (S₁.cut L₀) 𝔭 :=
    alphaL_split hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd
  have hαpos : 0 < alphaL h L₀ 𝔭 := alphaL_pos hK hF hs hd hL hLi h𝔭
  have hαC : 0 < alphaL h' (S₁.cut L₀) 𝔭 := alphaL_pos hK hF hs₁' hd₁' hC hCi h𝔭
  have hαN : alphaN h L₀ 𝔭 1 ≠ 0 := by
    intro h0
    rw [hsplit, h0, zero_mul] at hαpos
    exact lt_irrefl _ hαpos
  have hNsm : alphaN (algebraMap F K (n : F) • h) L₀ 𝔭 n =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 n * alphaN h L₀ 𝔭 1 := by
    have e := alphaN_smul hK hF hs hd hL hLi h𝔭 hn hs' hd' (by omega) one_ne_zero
    rwa [mul_one] at e
  have hLsm := alphaL_smul hK hF hs hd hL hLi h𝔭 hn hs' hd'
  have hvsm := PinA.vd_smul hK hF hs hd hL hLi h𝔭 hn
  have hvT : vd (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      vd h' (S₁.cut L₀) 𝔭 + finrank K V' * vF 𝔭 n := by
    rw [vd_locF hK hF hsc' hdc' hC hCic h𝔭]
    exact PinA.vd_smul hK hF hs₁' hd₁' hC hCi h𝔭 hn
  have hαT : alphaL (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 n * finrank K V' ^ 2) * alphaL h' (S₁.cut L₀) 𝔭 := by
    rw [← alphaL_smul hK hF hs₁' hd₁' hC hCi h𝔭 hn hsc' hdc']
    unfold alphaL
    simp only [akCount_locF hF _ (S₁.cut L₀) 𝔭 h𝔭]
  have hrep : IsLocReps S₁ L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} :=
    PinC.isLocReps_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd
  have hrep' : IsLocReps S L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} := isLocReps_scale hF hc S hL hLi h𝔭 hrep
  have hpsi : psiP S L₀ 𝔭 = lamP (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 := by
    rw [psiP_eq_sum hK hF hs' hd' S hL hLic h𝔭 hrep', Finset.sum_singleton, fibLoc_unscale hc,
      PinC.fibLoc_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd]
    simp
  refine ⟨L₀, hL, hLic, ?_, ?_⟩
  · unfold repRatio
    rw [hNsm, hLsm]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (mul_ne_zero (pow_ne_zero _ hN) hαN))
      (mul_ne_zero (pow_ne_zero _ hN) hαpos.ne')
  · rw [hpsi]
    unfold lamP repRatio
    rw [hvT, hαT, hNsm, hLsm, hvsm, hsplit, hvdC, ← hm, Nat.add_sub_cancel]
    have hA := hαC.ne'
    field_simp
    ring

end PinD

theorem liPin : LIPin := by
  unfold LIPin
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S 𝔭 n hs hd h𝔭 hn hx
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero _).2 hnF
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : V →ₗ⋆[K] V →ₗ[K] K, algebraMap F K (n : F) • h₀ = h :=
    ⟨(algebraMap F K (n : F))⁻¹ • h, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨h₀', rfl⟩ : ∃ h₀' : V' →ₗ⋆[K] V' →ₗ[K] K, algebraMap F K (n : F) • h₀' = h' :=
    ⟨(algebraMap F K (n : F))⁻¹ • h', by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  exact PinD.core hK hF n hn S hs hd h𝔭 hx

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem liStat_of (hR : LIRatio) (hP : LIPin) : LIStat := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L 𝔭 n hs hd h𝔭 hn hx hL hLi
  obtain ⟨L₀, hL₀, hL₀i, hR0, hpin⟩ := hP K F hK hF V V' h h' S 𝔭 n hs hd h𝔭 hn hx
  have hrat := hR K F hK hF V V' h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  rw [hpin] at hrat
  have key : psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
      alphaStd K 𝔭 (finrank K V - 1) * repRatio h L 𝔭 n := by
    apply mul_right_cancel₀ hR0
    rw [hrat]
    ring
  rw [key, repRatio, Nat.mul_add, pow_add]
  ring

theorem liStat : LIStat := liStat_of liRatio liPin

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem massConst_all (hH : HermRepUnram) (hLI : LIStat) {K F : Type} [Field K] [NumberField K]
    [StarRing K] [Field F] [NumberField F] [Algebra F K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ m : ℕ, 1 ≤ m →
      MassConst K F m (c₁ * ∏ j ∈ Finset.Icc 2 m, Formalism.HermitianLatticesTheory.massRatioRightSide K j) := by
  obtain ⟨c₁, hc₁, h1⟩ := exists_massConst_one (K := K) (F := F) hK hF
  refine ⟨c₁, hc₁, fun m hm => ?_⟩
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have he : Finset.Icc 2 (0 + 1) = ∅ := Finset.Icc_eq_empty (by norm_num)
      rw [he, Finset.prod_empty, mul_one]
      exact h1
    · have hc := ih hpos
      have hP : 0 < ∏ j ∈ Finset.Icc 2 m, Formalism.HermitianLatticesTheory.massRatioRightSide K j :=
        Finset.prod_pos fun j hj => massRatio_pos hK j (Finset.mem_Icc.mp hj).1
      have hstep := massConst_succ hH hLI hK hF (m := m + 1) (by omega) (mul_pos hc₁ hP)
        (by simpa using hc)
      rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc]
      exact hstep

theorem siegelMassRatio_of_LI (hH : HermRepUnram) (hLI : LIStat) : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  intro K _ _ _ hK M hM V V' _ _ _ _ _ _ _ _ h h' L L' hs hs' hL hL'
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hH hLI hK hF
  have := finiteDimensional_of_ortho hL
  have := finiteDimensional_of_ortho hL'
  have e1 := hall M (by omega) V h L hs (isTotPosDef_of_ortho hK hs hL) (finrank_of_ortho hL)
    (isLattice_of_ortho hL) (isIntegralLat_of_ortho hL)
  have e2 := hall (M - 1) (by omega) V' h' L' hs' (isTotPosDef_of_ortho hK hs' hL')
    (finrank_of_ortho hL') (isLattice_of_ortho hL') (isIntegralLat_of_ortho hL')
  rw [lamG_eq_one_of_ortho hK hF hs hL, mul_one] at e1
  rw [lamG_eq_one_of_ortho hK hF hs' hL', mul_one] at e2
  have hprod : ∏ j ∈ Finset.Icc 2 M, Formalism.HermitianLatticesTheory.massRatioRightSide K j =
      (∏ j ∈ Finset.Icc 2 (M - 1), Formalism.HermitianLatticesTheory.massRatioRightSide K j) * Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
    have := Finset.prod_Icc_succ_top (a := 2) (b := M - 1) (by omega)
      (fun j => Formalism.HermitianLatticesTheory.massRatioRightSide K j)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ M)] at this
  have hP : 0 < ∏ j ∈ Finset.Icc 2 (M - 1), Formalism.HermitianLatticesTheory.massRatioRightSide K j :=
    Finset.prod_pos fun j hj => massRatio_pos hK j (Finset.mem_Icc.mp hj).1
  rw [e1, e2, hprod, div_eq_iff (by positivity)]
  ring

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem siegelMassRatio : Formalism.HermitianLatticesTheory.SiegelMassRatio := siegelMassRatio_of_LI hermRepUnram liStat

end Formalism.HermitianLattices.Ext.L3
end
end
