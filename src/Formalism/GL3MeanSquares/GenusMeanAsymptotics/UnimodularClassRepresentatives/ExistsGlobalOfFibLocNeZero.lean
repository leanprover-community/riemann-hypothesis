import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem akCount_congr {A B : Submodule (𝓞 K) V} (e : ↥A ≃ₗ[𝓞 K] ↥B)
    (he : ∀ x y : ↥A, h (e x : V) (e y : V) = h (x : V) (y : V)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    akCount h B 𝔭 k = akCount h A 𝔭 k := by
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥B) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let ε := Submodule.Quotient.equiv _ _ e hmap
  have hε : ∀ x : ↥A, ε (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := fun x => rfl
  unfold akCount
  refine (Nat.card_congr (Equiv.subtypeEquiv ε.conj.toEquiv ?_)).symm
  intro X
  have hX : ∀ x : ↥A, (ε.conj X) (Submodule.Quotient.mk (e x)) = ε (X (Submodule.Quotient.mk x)) := by
    intro x
    rw [LinearEquiv.conj_apply_apply, ← hε, LinearEquiv.symm_apply_apply]
  constructor
  · intro H x y x' y' h1 h2
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective x'
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [he, he]
    refine H x y x' y' ?_ ?_
    · apply ε.injective
      rw [hε, ← hX]
      exact h1
    · apply ε.injective
      rw [hε, ← hX]
      exact h2
  · intro H x y x' y' h1 h2
    rw [← he, ← he x y]
    refine H (e x) (e y) (e x') (e y') ?_ ?_
    · change _ = (ε.conj X) _
      rw [hX, ← h1, hε]
    · change _ = (ε.conj X) _
      rw [hX, ← h2, hε]

theorem akCount_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) : akCount h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 k = akCount h T 𝔭 k :=
  akCount_congr (A := T) (B := Formalism.HermitianLatticesTheory.gmap g T) ((g.restrictScalars (𝓞 K)).submoduleMap T)
    (fun x y => hg (x : V) (y : V)) 𝔭 k

theorem alphaL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : alphaL h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = alphaL h T 𝔭 := by
  unfold alphaL
  simp only [akCount_gmap hg]

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem localFactor_map' {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : lamP h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = lamP h T 𝔭 := by
  unfold lamP
  rw [UnimodularLocalization.vd_gmap hg, alphaL_gmap hg]

theorem sum_locReps_eq (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s s' : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    (hsr' : IsLocReps S L 𝔭 s') :
    ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 = ∑ T ∈ s', (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have ex : ∀ T ∈ s, ∃! T₀, T₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T :=
    fun T hT => hsr'.2 T (hsr.1 T hT).1 (hsr.1 T hT).2.1 (hsr.1 T hT).2.2
  refine Finset.sum_bij (fun T hT => (ex T hT).choose) ?_ ?_ ?_ ?_
  · exact fun T hT => (ex T hT).choose_spec.1.1
  · intro T₁ h1 T₂ h2 e
    obtain ⟨g₁, hg₁, e₁⟩ := (ex T₁ h1).choose_spec.1.2
    obtain ⟨g₂, hg₂, e₂⟩ := (ex T₂ h2).choose_spec.1.2
    simp only at e
    rw [← e] at e₂
    have hu := hsr.2 T₂ (hsr.1 T₂ h2).1 (hsr.1 T₂ h2).2.1 (hsr.1 T₂ h2).2.2
    refine hu.unique ⟨h1, g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
      ⟨h2, 1, Subgroup.one_mem _, autSub_gmap_one _⟩
    rw [← e₁, ← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one, e₂]
  · intro T₀ h0
    obtain ⟨T, ⟨hT, g, hg, e⟩, -⟩ :=
      hsr.2 T₀ (hsr'.1 T₀ h0).1 (hsr'.1 T₀ h0).2.1 (hsr'.1 T₀ h0).2.2
    refine ⟨T, hT, ?_⟩
    refine (ex T hT).unique (ex T hT).choose_spec.1 ⟨h0, g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    rw [← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro T hT
    obtain ⟨g, hg, e⟩ := (ex T hT).choose_spec.1.2
    conv_lhs => rw [← e, GoodGenusOrbits.fibLoc_gmap hs S L 𝔭 hg, localFactor_map' hg]

theorem psiP_eq_sum' (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have hex : ∃ s, IsLocReps S L 𝔭 s := ⟨s, hsr⟩
  unfold psiP
  rw [dif_pos hex]
  exact sum_locReps_eq hs S L 𝔭 hex.choose_spec hsr

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finite_between {N D : Submodule (𝓞 K) V} (hN : Submodule.IsLattice K N)
    (hD : Submodule.IsLattice K D) (hND : N ≤ D) :
    {Λ : Submodule (𝓞 K) V | N ≤ Λ ∧ Λ ≤ D}.Finite := by
  have h1 := Formalism.HermitianLatticesTheory.finIntermediate V N.toAddSubgroup D.toAddSubgroup hND ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr hD.fg
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hD hN
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hnx _ q.2

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem finite_fibG (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'} (hΛ' : Submodule.IsLattice K Λ') : (fibG S L Λ').Finite := by
  have hN := (S.isLattice_adjoin_iff Λ').2 hΛ'
  have hD := (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (UnimodularLocalization.nondegenerate hd)
    Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
  by_cases hne : (fibG S L Λ').Nonempty
  · have key : ∀ Λ ∈ fibG S L Λ', S.adjoin Λ' ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin Λ') := by
      rintro Λ ⟨hg, hx, hc⟩
      have hΛi : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ :=
        ((Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).2.2 L Λ hL.fg hg.1.fg
          hg.2).2.mp hLi
      have := S.le_dual_of_mem hs hΛi hx
      rwa [hc] at this
    obtain ⟨Λ, hΛ⟩ := hne
    exact (finite_between hN hD ((key Λ hΛ).1.trans (key Λ hΛ).2)).subset key
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

theorem good_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (hx : S.x₀ ∈ B) :
    GoodGenusOrbits.Good F S B (S.cut B) := by
  have hc := StabilizerLattices.isLattice_cut S hB
  refine ⟨hc, fun 𝔮 h0 => ?_⟩
  have h1 := card_fibG_eq_prod (F := F) hK hF hs hd S hB hBi hc
  rw [tprod_of_exists_eq_zero ⟨𝔮, by rw [h0]; simp⟩] at h1
  have hfin := finite_fibG hs hd S hB hBi hc
  have hmem : B ∈ fibG S B (S.cut B) :=
    ⟨⟨hB, (Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range).1.refl B⟩, hx, rfl⟩
  have : Nat.card (fibG S B (S.cut B)) ≠ 0 := by
    have := hfin.to_subtype
    have : Nonempty (fibG S B (S.cut B)) := ⟨⟨B, hmem⟩⟩
    exact Nat.card_pos.ne'
  exact this (by exact_mod_cast h1)

def scaleSplit (S : VecSplit h h') (c : K) (hc : c ≠ 0) : VecSplit h h' where
  x₀ := c • S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := by
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_ne_zero hc (mul_ne_zero ((map_ne_zero _).mpr hc) S.hx₀)
  isom := S.isom
  orth := fun a => by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, S.orth, smul_zero]
  cover := fun v => by
    obtain ⟨d, a, rfl⟩ := S.cover v
    exact ⟨d / c, a, by rw [smul_smul, div_mul_cancel₀ _ hc]⟩

theorem fibLoc_scale (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsPrime) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {t : 𝓞 F} (ht : t ∉ 𝔭)
    (hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0) (T : Submodule (𝓞 K) V') :
    fibLoc (scaleSplit S _ hc) (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 T = fibLoc S L 𝔭 T := by
  unfold fibLoc
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Λ => ?_)
  refine and_congr_right fun hΛ => and_congr ?_ (and_congr_left fun _ => ?_)
  · rw [← LocalizedFibreSets.gmap_locF]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g' * g, Subgroup.mul_mem _ hg' hg, autSub_gmap_mul _ _ _⟩
    · rintro ⟨g', hg', rfl⟩
      refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
      rw [← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one]
  · change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ Λ ↔ _
    rw [algebraMap_smul]
    constructor
    · intro hx
      rw [← hΛ]
      exact (LocF.mem_locF_iff h𝔭 Λ _).mpr ⟨t, ht, hx⟩
    · exact fun hx => Λ.smul_mem _ hx

theorem exists_locReps' (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s := by
  by_cases H : ∀ T, fibLoc S L 𝔭 T = 0
  · exact ⟨∅, fun T hT => absurd hT (Finset.notMem_empty T), fun T _ _ h3 => absurd (H T) h3⟩
  · push Not at H
    obtain ⟨T₁, hT₁⟩ := H
    obtain ⟨g, hg, hx, -⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hT₁
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ _).mp hx
    have hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro e
      have e1 : algebraMap (𝓞 F) (𝓞 K) t = 0 := Formalism.HermitianLatticesTheory.genusCovol_hinj (by rw [e, map_zero])
      have e2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [e1, map_zero])
      exact ht (e2 ▸ 𝔭.zero_mem)
    have hB := LocalizedFibreSets.isLattice_gmap g hL
    have hBi := UnimodularLocalization.isIntegralLat_gmap hg hLi
    have hgood := good_cut (F := F) hK hF hs hd (scaleSplit S _ hc) hB hBi
      (by change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) • S.x₀ ∈ _
          rw [algebraMap_smul]; exact hx)
    obtain ⟨s, hs1⟩ := GoodGenusOrbits.exists_locReps hK hF hs hd (scaleSplit S _ hc) hB hBi hgood ⟨𝔭, h𝔭⟩
    refine ⟨s, ?_⟩
    unfold IsLocReps at hs1 ⊢
    simpa only [fibLoc_scale S L h𝔭.isPrime hg ht hc] using hs1

end Formalism.HermitianLattices.Ext.L3.BrB
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s :=
  BrB.exists_locReps' hK hF hs hd S hL hLi h𝔭

theorem psiP_eq_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 :=
  BrB.psiP_eq_sum' hs S L 𝔭 hsr

end Formalism.HermitianLattices.Ext.L3
end
end
