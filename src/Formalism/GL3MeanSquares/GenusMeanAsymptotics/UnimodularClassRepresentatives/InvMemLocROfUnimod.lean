import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibG (S : VecSplit h h') (L : Submodule (𝓞 K) V) (Λ' : Submodule (𝓞 K) V') :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Λ ∈ Formalism.HermitianLatticesTheory.genus h L ∧ S.x₀ ∈ Λ ∧ S.cut Λ = Λ'}

def IsFibReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (s' : Finset (Submodule (𝓞 K) V')) :
    Prop :=
  (∀ Λ' ∈ s', (fibG S L Λ').Nonempty) ∧
  ∀ Λ' : Submodule (𝓞 K) V', (fibG S L Λ').Nonempty →
    ∃! Λ₀, Λ₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g Λ₀ = Λ'

namespace StabilizerLattices

open SplitBAux

theorem pair_mem_of_fibG (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ') :
    (Λ, S.x₀) ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h (Λ, S.x₀) = (emb S Λ', S.x₀) :=
  ⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩

theorem fibG_of_pair_mem (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {p : Submodule (𝓞 K) V × V} (hp : p ∈ pairs h L (h S.x₀ S.x₀))
    (e : proj h p = (emb S Λ', S.x₀)) : p.1 ∈ fibG S L Λ' ∧ p.2 = S.x₀ := by
  obtain ⟨Λ, x⟩ := p
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  change Λ ⊓ perpO h x = emb S Λ' at e1
  change x = S.x₀ at e2
  subst e2
  rw [inf_perpO] at e1
  exact ⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩

theorem exists_move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) (p : Submodule (𝓞 K) V × V) :
    ∃ g : Formalism.HermitianLatticesTheory.isom h, p ∈ pairs h L (h S.x₀ S.x₀) →
      g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, S.x₀) ∧
      Formalism.HermitianLatticesTheory.gmap g.1 p.1 ∈ fibG S L (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := by
  by_cases hp : p ∈ pairs h L (h S.x₀ S.x₀)
  · have hne : p.2 ≠ 0 := by
      intro h0
      have := hp.2.2
      rw [h0] at this
      exact S.hx₀ (by simpa using this.symm)
    obtain ⟨g, hg, hgx⟩ := exists_isom_map_of_eq hK hs hd hne hp.2.2
    refine ⟨⟨g, hg⟩, fun _ => ⟨Prod.ext rfl hgx, OrbitRepresentatives.gmap_mem_genus hs hp.1 hg, ?_, rfl⟩⟩
    rw [← hgx]
    exact apply_mem_gmap g hp.2.1
  · exact ⟨1, fun h => absurd h hp⟩

theorem fibG_smul (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ')
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∈ fibG S L (Formalism.HermitianLatticesTheory.gmap g' Λ') := by
  refine ⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩
  · have := apply_mem_gmap (extOf S g') hΛ.2.1
    rwa [extOf_x₀] at this
  · rw [cut_gmap_extOf, hΛ.2.2]

theorem finite_stab_proj (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) {p : Submodule (𝓞 K) V × V}
    (hp : p ∈ pairs h L (h S.x₀ S.x₀)) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p) : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
  obtain ⟨hg1, hg2⟩ := hg hp
  have e : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
    rw [← proj_smul, hg1]
    exact (pair_mem_of_fibG S hg2).2
  have hlat : Submodule.IsLattice K (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := isLattice_cut S hg2.1.1
  have f1 : Finite (Formalism.ThetaLiftIndependence.autL h' (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1))) :=
    (Formalism.HermitianLatticesTheory.autFinite K V' h' (S.isSymm hs) (trace_pos (S.isTotPosDef hd)) _ hlat).to_subtype
  have f2 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (g • proj h p)) := by
    rw [e]
    exact Finite.of_equiv _ (stabPairEquiv hs S _).symm
  have f3 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p)) :=
    Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (g := g) (a := proj h p) rfl).symm.toEquiv
  exact Set.toFinite _

end StabilizerLattices

open StabilizerLattices SplitBAux in
theorem exists_fibReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : ∃ s', IsFibReps S L s' := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  choose γ hγ using exists_move hK hs hd S L
  obtain ⟨T, hT1, hT2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h')
    {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty}
    (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩)
    ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) V × V)))
    (sX.finite_toSet.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (hγ p (hsX p hp)).2⟩)
    (by
      rintro Λ' ⟨Λ, hΛ⟩
      obtain ⟨t, ⟨ht, k, hk⟩, -⟩ := hX _ (pair_mem_of_fibG S hΛ).1
      refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
      have e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀) := by
        rw [← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
      have := gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1
      rw [hΛ.2.2] at this
      exact ⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)
  refine ⟨T, hT1, fun Λ' hΛ' => ?_⟩
  have := hT2 Λ' hΛ'
  simp_rw [exists_smul_iff] at this
  exact this

open StabilizerLattices SplitBAux in
theorem repMass_eq_sum_fib (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s' : Finset (Submodule (𝓞 K) V')}
    (hs' : IsFibReps S L s') :
    repMass h L (h S.x₀ S.x₀) =
      ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  have hex := exists_classReps hs hd hL
  unfold repMass
  rw [dif_pos hex, ← sum_pairs_eq_rep hs hd (h S.x₀ S.x₀) hex.choose_spec hsX hX]
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (proj h) proj_smul
    (pairs h L (h S.x₀ S.x₀)) (proj h '' pairs h L (h S.x₀ S.x₀))
    (pairs_stable hs L _) (fun p hp => Set.mem_image_of_mem _ hp) sX
    (s'.image fun Λ' => (emb S Λ', S.x₀)) hsX
    (by
      intro u hu
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨Λ, hΛ⟩ := hs'.1 Λ' hΛ'
      exact ⟨_, (pair_mem_of_fibG S hΛ).1, (pair_mem_of_fibG S hΛ).2⟩)
    hX
    (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
      obtain ⟨hg1, hg2⟩ := hg hp
      have hgy : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
        rw [← proj_smul, hg1]
        exact (pair_mem_of_fibG S hg2).2
      obtain ⟨Λ₀, ⟨h₀, g', hg', e'⟩, huniq⟩ := hs'.2 _ ⟨_, hg2⟩
      refine ⟨(emb S Λ₀, S.x₀), ⟨Finset.mem_image.mpr ⟨Λ₀, h₀, rfl⟩,
        g⁻¹ * ⟨extOf S g', extOf_mem_isom hs S hg'⟩, ?_⟩, ?_⟩
      · have e0 : (⟨extOf S g', extOf_mem_isom hs S hg'⟩ : Formalism.HermitianLatticesTheory.isom h) • (emb S Λ₀, S.x₀) =
            g • proj h p := by
          rw [hgy, ← e', ← gmap_extOf_emb]
          exact Prod.ext rfl (extOf_x₀ S g')
        rw [mul_smul, e0, inv_smul_smul]
      · rintro t ⟨ht, k, hk⟩
        obtain ⟨Λ₁, h₁, rfl⟩ := Finset.mem_image.mp ht
        have e : (g * k) • (emb S Λ₁, S.x₀) =
            (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
          rw [mul_smul, hk, hgy]
        obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
        have := gmap_res S (g * k).1 (g * k).2 e2 e1
        rw [cut_emb, cut_emb] at this
        rw [huniq Λ₁ ⟨h₁, _, res_mem_isom S _ _ _, this⟩])
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact finite_stab_proj hK hs hd S L hp)
  rw [key, Finset.sum_image (fun A _ B _ e => emb_injective S (Prod.ext_iff.mp e).1)]
  refine Finset.sum_congr rfl fun Λ' _ => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V //
      p ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h p = (emb S Λ', S.x₀)} = Nat.card (fibG S L Λ') :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, (fibG_of_pair_mem S p.2.1 p.2.2).1⟩
        invFun := fun Λ => ⟨(Λ.1, S.x₀), pair_mem_of_fibG S Λ.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl (fibG_of_pair_mem S p.2.1 p.2.2).2.symm)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabPairEquiv hs S Λ')]

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibSet (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : Set (Submodule (𝓞 K) V) :=
  {Λ | locF 𝔭 Λ = Λ ∧ (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
    S.cut Λ = locF 𝔭 T}

theorem fibLoc_eq_card (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : fibLoc S L 𝔭 T = Nat.card (fibSet S L 𝔭 T) := rfl

theorem le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

theorem locF_idem (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) : locF 𝔭 (locF 𝔭 L) = locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_locS_idem _ L

theorem gmap_locF (g : V ≃ₗ[K] V) (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) :=
  Formalism.HermitianLatticesTheory.gmap_locS_comm g _ L

theorem cut_locF (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    S.cut (locF 𝔭 Λ) = locF 𝔭 (S.cut Λ) := by
  ext a
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower]
    exact hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower] at hx
    exact hx

theorem isLattice_gmap (g : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 K) V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem form_smul_smul (s t : 𝓞 K) (x y : V) :
    h (s • x) (t • y) = (conjO K s * t) • h x y := by
  have e : algebraMap (𝓞 K) K (conjO K s) = starRingEnd K (algebraMap (𝓞 K) K s) := rfl
  rw [← algebraMap_smul K s x, ← algebraMap_smul K t y, map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, Algebra.smul_def, map_mul, e]
  ring

theorem form_mem_locR {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (P : Ideal (𝓞 K))
    {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) P L) (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P L) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨conjO K s * t, Submonoid.mul_mem _ (conjO_mem_hcompl P hs) ht, ?_⟩
  rw [← form_smul_smul]
  exact hLi _ hx _ hy

theorem form_mem_locR_gmap {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (P : Ideal (𝓞 K)) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V}
    (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) P L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) P L)) :
    h x y ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
  rw [SplitBAux.mem_gmap_iff] at hx hy
  have := form_mem_locR hLi P hx hy
  rwa [SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg)] at this

theorem smul_mem_of_loc_eq {P : Ideal (𝓞 K)} {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.loc (K := K) P Λ = Λ) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P) {x : V}
    (hx : x ∈ Λ) : c • x ∈ Λ := by
  obtain ⟨s, hs, hc⟩ := hc
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  rw [← hΛ]
  refine ⟨s, hs, ?_⟩
  rw [← smul_assoc, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hx

theorem comb_mem_dualAt_iff (hs : h.IsSymm) (S : VecSplit h h') (p : Ideal (𝓞 K))
    (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) ↔
      c * h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧
        a ∈ Formalism.HermitianLatticesTheory.dualAt h' p (Formalism.HermitianLatticesTheory.loc (K := K) p L') := by
  rw [mem_dualAt_iff', mem_dualAt_iff']
  constructor
  · intro H
    refine ⟨?_, fun b hb => ?_⟩
    · have := H ((1 : K) • S.x₀ + S.ι 0)
        ((S.comb_mem_loc_adjoin_iff p L' 1 0).mpr ⟨one_mem_locR p, Submodule.zero_mem _⟩)
      rwa [SplitBAux.h_decomp hs S, star_one, one_mul, map_zero, LinearMap.zero_apply, add_zero] at this
    · have := H ((0 : K) • S.x₀ + S.ι b)
        ((S.comb_mem_loc_adjoin_iff p L' 0 b).mpr ⟨Submodule.zero_mem _, hb⟩)
      rwa [SplitBAux.h_decomp hs S, star_zero, zero_mul, zero_mul, zero_add] at this
  · rintro ⟨hc, ha⟩ y hy
    obtain ⟨d, b, rfl⟩ := S.cover y
    obtain ⟨hd, hb⟩ := (S.comb_mem_loc_adjoin_iff p L' d b).mp hy
    rw [SplitBAux.h_decomp hs S, mul_assoc]
    exact Submodule.add_mem _ (mul_mem_locR p (star_mem_locR p hd) hc) (ha b hb)

theorem inv_mem_locR_of_unimod (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L')) :
    (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  have h1 : (h S.x₀ S.x₀)⁻¹ • S.x₀ + S.ι 0 ∈
      Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) := by
    rw [comb_mem_dualAt_iff hs, inv_mul_cancel₀ S.hx₀]
    exact ⟨one_mem_locR p, Submodule.zero_mem _⟩
  rw [hU] at h1
  exact ((S.comb_mem_loc_adjoin_iff p L' _ 0).mp h1).1

theorem unimod_adjoin (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hn : h S.x₀ S.x₀ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) p)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L') : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hU ⊢
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [comb_mem_dualAt_iff hs, S.comb_mem_loc_adjoin_iff, hU]
  refine and_congr_left fun _ => ⟨fun hc => ?_, fun hc => mul_mem_locR p hc hn⟩
  have := mul_mem_locR p hc hn'
  rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this

theorem isIntegralLat_adjoin (hs : h.IsSymm) (S : VecSplit h h')
    (hn : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K)) {L' : Submodule (𝓞 K) V'}
    (hL' : Formalism.HermitianLatticesTheory.IsIntegralLat h' L') : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') := by
  intro x hx y hy
  obtain ⟨r, a, ha, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
  obtain ⟨t, b, hb, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hn
  obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hL' a ha b hb)
  rw [SplitBAux.h_decomp hs S, ← hn, ← hw]
  refine Submodule.mem_one.mpr ⟨conjO K r * t * n + w, ?_⟩
  rw [map_add, map_mul, map_mul]
  rfl

theorem exists_max_over {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  have := h𝔭
  refine Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔭 ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  exact bot_le

theorem fibSet_eq_singleton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {Λ' : Submodule (𝓞 K) V'}
    (hN : Submodule.IsLattice K (S.adjoin Λ')) (hNi : Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ'))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hvL : vd h L 𝔭 = 0) (hvN : vd h (S.adjoin Λ') 𝔭 = 0) :
    fibSet S L 𝔭 Λ' = {locF 𝔭 (S.adjoin Λ')} := by
  obtain ⟨P, hP, rfl⟩ := exists_max_over (K := K) h𝔭
  have hUN := (isUnimodularAt_iff_vd hK hF hs hd hN hNi hP).2 hvN
  have hinv := inv_mem_locR_of_unimod hs S hUN
  ext Λ
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, ⟨g, hg, h2⟩, h3, h4⟩
    rw [locF_eq_loc hK hF hP] at h1 h2 h4 ⊢
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [S.comb_mem_loc_adjoin_iff, ← h4, VecSplit.mem_cut_iff]
    constructor
    · intro hv
      have hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
        have h5 : h S.x₀ (c • S.x₀ + S.ι a) ∈ Formalism.HermitianLatticesTheory.locR (K := K) P :=
          form_mem_locR_gmap hLi P hg (h2 ▸ h3) (h2 ▸ hv)
        rw [S.h_x₀_comb] at h5
        have := mul_mem_locR P h5 hinv
        rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this
      refine ⟨hc, ?_⟩
      have := Λ.sub_mem hv (smul_mem_of_loc_eq h1 hc h3)
      rwa [add_sub_cancel_left] at this
    · rintro ⟨hc, ha⟩
      exact Λ.add_mem (smul_mem_of_loc_eq h1 hc h3) ha
  · rintro rfl
    refine ⟨locF_idem _ _, exists_isom_locF_of_vd_zero hK hF hs hd hL hN hLi hNi h𝔭 hvL hvN,
      le_locF _ _ (S.x₀_mem_adjoin Λ'), ?_⟩
    rw [cut_locF, S.cut_adjoin]

theorem notMem_of_vF_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hv : vF 𝔭 n = 0) : n ∉ 𝔭 := by
  intro hn
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
    by_contra hb
    apply hn0
    have h1 : n ∈ (⨅ i : ℕ, 𝔭 ^ i) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [not_bddAbove_iff] at hb
      obtain ⟨e, he, hie⟩ := hb i
      exact Ideal.pow_le_pow_right hie.le he
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top, Ideal.mem_bot] at h1
  have h1 : 1 ≤ vF 𝔭 n := le_csSup hb (by simpa using hn)
  omega

end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
end
end
