import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinrankRingOfIntegers
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeVdLeOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralAtLocF

section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb

open Subgroup

variable {G : Type*} [Group G]

private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]

theorem relIndex_eq_of_cover (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩

theorem index_tube (H S C H' : Subgroup G) (hS : S ≤ H) (hC : C ≤ H) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) :
    S.relIndex H * C.relIndex H' = C.relIndex H * S.relIndex C := by
  rw [← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm,
    relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]

theorem relIndex_cocycle (A B C : Subgroup G) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hCB : B.relIndex C ≠ 0) :
    B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  have hBA' : B.relIndex A ≠ 0 := relIndex_ne_zero_trans hCB hAC
  have hAC' : A.relIndex C ≠ 0 := relIndex_ne_zero_trans hBA hCB
  have orbitMap_conj_smul_one := relIndex_inf_mul_relIndex C B A
  have orbitMap_conj_smul_two := relIndex_inf_mul_relIndex B C A
  have eB1 := relIndex_inf_mul_relIndex A C B
  have eB2 := relIndex_inf_mul_relIndex C A B
  have eC1 := relIndex_inf_mul_relIndex B A C
  have eC2 := relIndex_inf_mul_relIndex A B C
  have EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A := by
    rw [inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]
  have EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B := by
    rw [inf_comm B C, eB1, eB2, inf_comm]
  have EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C := by
    rw [eC1, eC2, inf_comm]
  have hu : C.relIndex (A ⊓ B) ≠ 0 := by
    rw [inf_comm]
    exact left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')
  have hv : B.relIndex (A ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')
  have hw : A.relIndex (B ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))
  calc C.relIndex (A ⊓ B) * B.relIndex (A ⊓ C) * A.relIndex (B ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (C.relIndex (A ⊓ B) * B.relIndex A) * (A.relIndex (B ⊓ C) * C.relIndex B) *
          (B.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (B.relIndex (A ⊓ C) * C.relIndex A) * (C.relIndex (A ⊓ B) * A.relIndex B) *
          (A.relIndex (B ⊓ C) * B.relIndex C) := by rw [EA, EB, EC]
    _ = _ := by ring

theorem ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  revert hf hd
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih hf hd
  have hfa : (f a).Finite := hf a (Finset.mem_insert_self a s)
  have hfs : (⋃ i ∈ s, f i).Finite :=
    Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)
  have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs,
    ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]

theorem ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y

theorem sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by
  classical
  have hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) =
      ∑ t ∈ sX.filter (fun t => π t = y),
        ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) := by
    intro y hy
    have hfib : {x | x ∈ A ∧ π x = y} =
        ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hxA, hxy⟩
        obtain ⟨t, ⟨ht, g, hgt⟩, -⟩ := hX x hxA
        have h1 : π t = y := hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩
        refine ⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩
        rw [← h1, ← hπ, hgt, hxy, h1]
      · rintro ⟨t, ⟨ht, h1⟩, g, hg, rfl⟩
        refine ⟨hA g t (hsX t ht).1, ?_⟩
        rw [hπ, h1, hg]
    have hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite := by
      intro t ht
      rw [Finset.mem_filter] at ht
      apply Set.finite_of_ncard_ne_zero
      rw [ncard_orb, ← ht.2]
      exact hfin t ht.1
    have hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint
        (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x}) := by
      intro t ht t' ht' hne
      refine Set.disjoint_left.2 ?_
      rintro x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩
      rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨t0, -, huniq⟩ := hX (g • t) (hA g t (hsX t ht.1).1)
      exact hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)
    have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard :=
      by first | exact Nat.card_coe_set_eq _ | exact (Set.ncard_def _).symm
    rw [hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ncard_orb, ht.2]
  symm
  calc ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y
      = ∑ y ∈ sY, ∑ t ∈ sX.filter (fun t => π t = y),
          ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) * w (π t) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hcard y hy, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _

end Formalism.HermitianLattices.Ext.L3.LIOrb
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem pow_smul_anti (𝔭 : Ideal (𝓞 F)) (A : Submodule (𝓞 K) V) {i j : ℕ} (hij : i ≤ j) :
    ((extP K 𝔭) ^ j • A : Submodule (𝓞 K) V) ≤ (extP K 𝔭) ^ i • A := Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)

theorem exists_pow_smul_le {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ((extP K 𝔭) ^ r • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hc
  refine ⟨r, ?_⟩
  have key : extP K 𝔭 ^ r ≤ (locF 𝔭 M₂).colon (locF 𝔭 M₁ : Set V) := by
    unfold extP
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 M₁ x).1 hx
    obtain ⟨d, hd⟩ := hdvd a ha
    refine (LocalSpans.mem_locF 𝔭 M₂ _).2
      ⟨u * s, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu hs, ?_⟩
    have e : algebraMap (𝓞 F) (𝓞 K) (u * s) • algebraMap (𝓞 F) (𝓞 K) a • x =
        algebraMap (𝓞 F) (𝓞 K) d • (n • (algebraMap (𝓞 F) (𝓞 K) s • x)) := by
      rw [← LocF.algebraMap_intCast_smul (F := F) (K := K) n]
      simp only [smul_smul, ← map_mul]
      congr 2
      linear_combination s * hd
    rw [e]
    exact M₂.smul_mem _ (hnx _ hsx)
  rw [Submodule.smul_le]
  intro a ha x hx
  exact Submodule.mem_colon.1 (key ha) x hx

set_option linter.unusedVariables false in
theorem locF_inf {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A B : Submodule (𝓞 K) V}
    (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B) : locF 𝔭 (A ⊓ B) = A ⊓ B := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (LocF.locF_mono 𝔭 inf_le_left).trans hA.le
    · exact (LocF.locF_mono 𝔭 inf_le_right).trans hB.le
  · exact LocF.le_locF 𝔭 _

theorem locF_inf_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A B : Submodule (𝓞 K) V) :
    locF 𝔭 (A ⊓ B) = locF 𝔭 A ⊓ locF 𝔭 B := by
  have := h𝔭.isPrime
  apply le_antisymm
  · exact le_inf (LocF.locF_mono 𝔭 inf_le_left) (LocF.locF_mono 𝔭 inf_le_right)
  · rintro x ⟨h1, h2⟩
    obtain ⟨s, hs, hsx⟩ := (LocalSpans.mem_locF 𝔭 A x).1 h1
    obtain ⟨t, ht, htx⟩ := (LocalSpans.mem_locF 𝔭 B x).1 h2
    refine (LocalSpans.mem_locF 𝔭 _ x).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, map_mul, mul_smul]
      exact A.smul_mem _ hsx
    · rw [map_mul, mul_smul]
      exact B.smul_mem _ htx

theorem isLattice_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) : Submodule.IsLattice K (M₁ ⊓ M₂) where
  fg := by
    have : Module.Finite (𝓞 K) ↥M₁ := Module.Finite.iff_fg.2 hM₁.fg
    have : IsNoetherian (𝓞 K) ↥M₁ := inferInstance
    have : IsNoetherian (𝓞 K) ↥(M₁ ⊓ M₂) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM₁ hM₂
    rw [eq_top_iff, ← hM₁.span_eq_top, Submodule.span_le]
    intro x hx
    have h1 : n • x ∈ Submodule.span K ((M₁ ⊓ M₂ : Submodule (𝓞 K) V) : Set V) :=
      Submodule.subset_span ⟨zsmul_mem hx n, hnx x hx⟩
    have h2 := Submodule.smul_mem _ ((n : K)⁻¹) h1
    rwa [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn),
      one_smul] at h2

theorem finite_quot_inf {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂) ⧸
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁ ⊓ locF 𝔭 M₂))) := by
  rw [← locF_inf_locF h𝔭]
  exact finite_quot (isLattice_inf hM₁ hM₂) h𝔭 k

theorem apply_mem_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {g : V ≃ₗ[K] V}
    (hg : g ∈ autSub h A) {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  rw [← h2]
  exact Submodule.mem_map_of_mem hz

theorem apply_mem_smul_of_mem_autSub {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V}
    {g : V ≃ₗ[K] V} (hg : g ∈ autSub h A) (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ I • A) :
    g z ∈ I • A := by
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg.2
  have h1 : g z ∈ (I • A).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  rwa [Submodule.map_smul'', h2] at h1

theorem congr_apply_mem {M₁ M₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {r₁ r₂ j : ℕ} (h1 : ((extP K 𝔭) ^ r₁ • locF 𝔭 M₁ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₂)
    (h2 : ((extP K 𝔭) ^ r₂ • locF 𝔭 M₂ : Submodule (𝓞 K) V) ≤ locF 𝔭 M₁) (hj : r₂ + r₁ ≤ j)
    (g : V ≃ₗ[K] V)
    (hg : ∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V))
    {z : V} (hz : z ∈ locF 𝔭 M₂) : g z ∈ locF 𝔭 M₂ := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  have hz1 : algebraMap F K (π : F) ^ r₂ • z ∈ locF 𝔭 M₁ :=
    h2 ((D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).2 ⟨z, hz, rfl⟩)
  have h3 := pow_smul_anti 𝔭 (locF 𝔭 M₁) hj (hg _ hz1)
  rw [pow_add, Submodule.mul_smul] at h3
  have h4 := Submodule.smul_mono (le_refl (extP K 𝔭 ^ r₂)) h1 h3
  obtain ⟨w, hw, e⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' M₂).1 h4
  rw [map_smul, ← smul_sub] at e
  have e' : g z - z = w :=
    smul_right_injective V (pow_ne_zero r₂ (D2.unif_ne_zero (K := K) hπ')) e
  have : g z = w + z := by rw [← e']; abel
  rw [this]
  exact add_mem hw hz

theorem exists_congr_mem_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ g ∈ autSub h (locF 𝔭 M₁),
      (∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V)) →
      g ∈ autSub h (locF 𝔭 M₂) := by
  obtain ⟨r₁, h1⟩ := exists_pow_smul_le hM₁ hM₂ h𝔭
  obtain ⟨r₂, h2⟩ := exists_pow_smul_le hM₂ hM₁ h𝔭
  refine ⟨r₂ + r₁, fun j hj g hg hc => ⟨hg.1, ?_⟩⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact congr_apply_mem h𝔭 h1 h2 hj g hc hz
  · intro x hx
    have hc' : ∀ z ∈ locF 𝔭 M₁,
        g.symm z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V) := by
      intro z hz
      have hz' : g.symm z ∈ locF 𝔭 M₁ := apply_mem_of_mem_autSub (inv_mem hg) hz
      have := neg_mem (hc _ hz')
      rwa [LinearEquiv.apply_symm_apply, neg_sub] at this
    exact ⟨g.symm x, congr_apply_mem h𝔭 h1 h2 hj g.symm hc' hx, by simp⟩

theorem orbCount_eq_relIndex (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) :
    orbCount h A B = (autSub h B).relIndex (autSub h A) := by
  let _ : MulAction (V ≃ₗ[K] V) (Submodule (𝓞 K) V) :=
    { smul := fun g L => Formalism.HermitianLatticesTheory.gmap g L
      one_smul := autSub_gmap_one
      mul_smul := autSub_gmap_mul }
  have hst : MulAction.stabilizer ↥(autSub h A) B = (autSub h B).subgroupOf (autSub h A) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      exact ⟨g.2.1, hg⟩
    · intro hg
      exact hg.2
  rw [Subgroup.relIndex, ← hst, Subgroup.index_eq_card,
    ← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ B)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro C
  constructor
  · rintro ⟨g, hg, hA, hB⟩
    exact ⟨⟨g, hg, hA⟩, hB⟩
  · rintro ⟨⟨g, hg, hA⟩, hB⟩
    exact ⟨g, hg, hA, hB⟩

theorem relIndex_ne_zero_of_map {G X : Type*} [Group G] [Finite X] (H Γ : Subgroup G) (f : H → X)
    (hf : ∀ a b : H, f a = f b → (a : G)⁻¹ * b ∈ Γ) : Γ.relIndex H ≠ 0 := by
  classical
  show (Γ.subgroupOf H).index ≠ 0
  have hfin : Finite (H ⧸ Γ.subgroupOf H) := by
    let g : Set.range f → H ⧸ Γ.subgroupOf H := fun x => QuotientGroup.mk x.2.choose
    apply Finite.of_surjective g
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      refine ⟨⟨f a, a, rfl⟩, ?_⟩
      show QuotientGroup.mk _ = QuotientGroup.mk a
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hf _ _ (⟨f a, a, rfl⟩ : Set.range f).2.choose_spec
  exact Subgroup.index_ne_zero_of_finite

def resA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (g : autSub h A) : ↥A →ₗ[𝓞 K] ↥A :=
  (((g : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict
    (fun _ hz => apply_mem_of_mem_autSub g.2 hz)

def redA {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K)) (g : autSub h A) :
    (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) →ₗ[𝓞 K] (↥A ⧸ (I • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (resA g) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

theorem sub_mem_of_redA_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} (I : Ideal (𝓞 K))
    {a b : autSub h A} (e : redA I a = redA I b) {z : V} (hz : z ∈ A) :
    (b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z ∈ I • A := by
  have h1 := congrArg (fun φ => φ (Submodule.Quotient.mk (⟨z, hz⟩ : ↥A))) e
  simp only [redA, Submodule.mapQ_apply] at h1
  rw [eq_comm, Submodule.Quotient.eq] at h1
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) h1
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at h2
  simp only [Submodule.subtype_apply] at h2
  exact h2

theorem relIndex_autSub_ne_zero (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  have := finite_quot hM₁ h𝔭 j
  have : Finite ((↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁))) →ₗ[𝓞 K]
      (↥(locF 𝔭 M₁) ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 M₁)))) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine relIndex_ne_zero_of_map _ _ (redA (extP K 𝔭 ^ j)) fun a b e => ?_
  refine hj j le_rfl _ (mul_mem (inv_mem a.2) b.2) fun z hz => ?_
  have h1 := apply_mem_smul_of_mem_autSub (inv_mem a.2) _ (sub_mem_of_redA_eq _ e hz)
  have h2 : ((a : V ≃ₗ[K] V)⁻¹ * (b : V ≃ₗ[K] V)) z - z =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) z - (a : V ≃ₗ[K] V) z) := by
    rw [map_sub]
    change _ = (a : V ≃ₗ[K] V).symm _ - (a : V ≃ₗ[K] V).symm _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rw [h2]
  exact h1

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

def mu (𝔮 I : Ideal (𝓞 F)) : ℕ := sSup {e : ℕ | I ≤ 𝔮 ^ e}

theorem mu_mul {𝔮 : Ideal (𝓞 F)} (h𝔮 : 𝔮.IsMaximal) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) : mu 𝔮 (I * J) = mu 𝔮 I + mu 𝔮 J := by
  let v := BrA.maxEquiv F ⟨𝔮, h𝔮⟩
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have e : ∀ X : Ideal (𝓞 F), X ≠ ⊥ → mu 𝔮 X = multiplicity v.asIdeal X :=
    fun X hX => BrA.sSup_le_pow v hX
  rw [e _ hIJ, e _ hI, e _ hJ]
  exact multiplicity_mul v.prime (FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hIJ)

theorem discrIdeal_mono {h : V →ₗ⋆[K] V →ₗ[K] K} {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    discrIdeal h A ≤ discrIdeal h B := by
  unfold discrIdeal
  apply Ideal.span_mono
  rintro z ⟨x, hx, e⟩
  exact ⟨x, fun i => hAB (hx i), e⟩

theorem exists_pow_smul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V}
    (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N := by
  have hp := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hn'
  refine ⟨r, fun a ha y hy => ?_⟩
  rw [LocF.mem_locF_iff hp]
  refine ⟨u, hu, ?_⟩
  obtain ⟨d, hd⟩ := hdvd a ha
  rw [smul_smul, ← map_mul, hd, map_mul, mul_comm, mul_smul, LocF.algebraMap_intCast_smul]
  exact N.smul_mem _ (hnx y hy)

theorem mem_locF_of_smul {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {t : 𝓞 F}
    (ht : t ∉ 𝔭) {x : V} (hx : ι t • x ∈ locF 𝔭 N) : x ∈ locF 𝔭 N := by
  obtain ⟨s, hs, h⟩ := (LocF.mem_locF_iff hp N _).1 hx
  refine (LocF.mem_locF_iff hp N x).2 ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem pow_smul_locF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) {a : 𝓞 F} (ha : a ∈ 𝔭 ^ r) {x : V}
    (hx : x ∈ locF 𝔭 M) : ι a • x ∈ locF 𝔭 N := by
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).1 hx
  apply mem_locF_of_smul h𝔭.isPrime ht
  rw [smul_comm]
  exact hr a ha _ htx

theorem locF_inf_of_ne {𝔭 𝔮 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (h𝔮 : 𝔮.IsMaximal) (hne : 𝔮 ≠ 𝔭)
    {M N : Submodule (𝓞 K) V} {r : ℕ} (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    locF 𝔮 (M ⊓ locF 𝔭 N) = locF 𝔮 M := by
  apply le_antisymm (LocF.locF_mono 𝔮 inf_le_left)
  have hnle : ¬ 𝔭 ^ r ≤ 𝔮 := fun hle =>
    hne (h𝔭.eq_of_le h𝔮.ne_top (h𝔮.isPrime.le_of_pow_le hle)).symm
  obtain ⟨a, ha, ha𝔮⟩ := SetLike.not_le_iff_exists.mp hnle
  have hM : M ≤ locF 𝔮 (M ⊓ locF 𝔭 N) := by
    intro y hy
    exact (LocF.mem_locF_iff h𝔮.isPrime _ y).2
      ⟨a, ha𝔮, Submodule.mem_inf.2 ⟨M.smul_mem _ hy, hr a ha y hy⟩⟩
  calc locF 𝔮 M ≤ locF 𝔮 (locF 𝔮 (M ⊓ locF 𝔭 N)) := LocF.locF_mono 𝔮 hM
    _ = _ := LocF.locF_idem 𝔮 _

theorem locF_inf (𝔭 : Ideal (𝓞 F)) (hp : 𝔭.IsPrime) (M N : Submodule (𝓞 K) V) :
    locF 𝔭 (M ⊓ locF 𝔭 N) = locF 𝔭 M ⊓ locF 𝔭 N := by
  apply le_antisymm
  · refine le_inf (LocF.locF_mono 𝔭 inf_le_left) ?_
    calc locF 𝔭 (M ⊓ locF 𝔭 N) ≤ locF 𝔭 (locF 𝔭 N) := LocF.locF_mono 𝔭 inf_le_right
      _ = locF 𝔭 N := LocF.locF_idem 𝔭 N
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp M x).1 (Submodule.mem_inf.1 hx).1
    exact (LocF.mem_locF_iff hp _ x).2 ⟨t, ht, Submodule.mem_inf.2
      ⟨htx, (locF 𝔭 N).smul_mem _ (Submodule.mem_inf.1 hx).2⟩⟩

theorem card_eq_relIndex {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {M N : Submodule (𝓞 K) V} {r : ℕ}
    (hr : ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, ι a • y ∈ locF 𝔭 N) :
    Nat.card (↥(locF 𝔭 M) ⧸ (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M)) =
      (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup := by
  set B' := (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M) with hB'
  let φ : ↥M →ₗ[𝓞 K] ↥(locF 𝔭 M) ⧸ B' := B'.mkQ ∘ₗ Submodule.inclusion (LocF.le_locF 𝔭 M)
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
    obtain ⟨c, hc, hcx⟩ := localizedQuotients.exists_approx h𝔭 M r x.2
    refine ⟨⟨_, hcx⟩, ?_⟩
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    change (ι c • (x : V) - (x : V)) ∈ locF 𝔭 M ⊓ locF 𝔭 N
    have e : ι c • (x : V) - (x : V) = ι (c - 1) • (x : V) := by
      rw [map_sub, map_one, sub_smul, one_smul]
    rw [e]
    exact Submodule.mem_inf.2 ⟨(locF 𝔭 M).smul_mem _ x.2, pow_smul_locF h𝔭 hr hc x.2⟩
  have hker : (LinearMap.ker φ).toAddSubgroup =
      (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
    simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change ((y : V) ∈ locF 𝔭 M ⊓ locF 𝔭 N) ↔ (y : V) ∈ M ⊓ locF 𝔭 N
    rw [Submodule.mem_inf, Submodule.mem_inf]
    exact ⟨fun h => ⟨y.2, h.2⟩, fun h => ⟨LocF.le_locF 𝔭 M y.2, h.2⟩⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
  exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm

theorem relIndex_ne_zero {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hN : Submodule.IsLattice K N) (𝔭 : Ideal (𝓞 F)) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
  have f1 : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have f2 : Module.Finite ℤ M := Module.Finite.trans (𝓞 K) M
  have f3 : AddGroup.FG M.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
  have : Finite (↥M.toAddSubgroup ⧸ (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup) := by
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact Submodule.mem_inf.2 ⟨zsmul_mem q.2 n, LocF.le_locF 𝔭 N (hnx _ q.2)⟩
  exact AddSubgroup.index_ne_zero_of_finite

theorem vd_mul {𝔭 : Ideal (𝓞 F)} (hF : IsFixF K F) [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (hN : Submodule.IsLattice K N) (h𝔭 : 𝔭.IsMaximal) :
    (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup * Ideal.absNorm 𝔭 ^ vd h M 𝔭 =
      Ideal.absNorm 𝔭 ^ vd h (M ⊓ locF 𝔭 N) 𝔭 := by
  set M'' := M ⊓ locF 𝔭 N with hM''
  set n := M''.toAddSubgroup.relIndex M.toAddSubgroup with hn
  have hn0 : n ≠ 0 := relIndex_ne_zero hM hN 𝔭
  obtain ⟨r, hr⟩ := exists_pow_smul h𝔭 hM hN
  have hle : M'' ≤ M := inf_le_left
  have hnorm := BallB.absNorm_discrIdeal_of_le hK hMi (Module.finBasis K V) n M'' hle rfl hn0
  rw [BrA.discrIdeal_eq_map hF hs M'', BrA.discrIdeal_eq_map hF hs M, BrA.absNorm_map hK hF,
    BrA.absNorm_map hK hF, ← mul_pow] at hnorm
  have hnorm' : Ideal.absNorm (BrA.discrF F h M'') = n * Ideal.absNorm (BrA.discrF F h M) :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hnorm
  have hD : BrA.discrF F h M ≠ ⊥ := by
    intro hb
    apply LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hM hMi
    rw [BrA.discrIdeal_eq_map hF hs M, hb, Ideal.map_bot]
  have hdvd : BrA.discrF F h M ∣ BrA.discrF F h M'' := by
    rw [Ideal.dvd_iff_le]
    exact Ideal.comap_mono (discrIdeal_mono hle)
  obtain ⟨J, hJ⟩ := hdvd
  have hDn : Ideal.absNorm (BrA.discrF F h M) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hJn : Ideal.absNorm J = n := by
    rw [hJ, map_mul, mul_comm] at hnorm'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hDn) hnorm'
  have hJ0 : J ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot] at hJn
    exact hn0 hJn.symm
  have hother : ∀ 𝔮 : {𝔮 : Ideal (𝓞 F) // 𝔮.IsMaximal}, 𝔮.1 ≠ 𝔭 → mu 𝔮.1 J = 0 := by
    intro 𝔮 hne
    have e1 : vd h M'' 𝔮.1 = vd h M 𝔮.1 := by
      rw [← localizedQuotients.vd_locF hF h M'' 𝔮.2, hM'', locF_inf_of_ne h𝔭 𝔮.2 hne hr, localizedQuotients.vd_locF hF h M 𝔮.2]
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ] at e1
    change mu 𝔮.1 (_ * J) = mu 𝔮.1 _ at e1
    rw [mu_mul 𝔮.2 hD hJ0] at e1
    omega
  have hJn' : Ideal.absNorm J = Ideal.absNorm 𝔭 ^ mu 𝔭 J := by
    have := BrA.absNorm_eq_tprod hJ0
    rw [tprod_eq_mulSingle ⟨𝔭, h𝔭⟩] at this
    · have h3 : (Ideal.absNorm J : ℝ) = ((Ideal.absNorm 𝔭 ^ mu 𝔭 J : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact this
      exact_mod_cast h3
    · intro 𝔮 hne
      rw [show sSup {e : ℕ | J ≤ 𝔮.1 ^ e} = mu 𝔮.1 J from rfl,
        hother 𝔮 (fun h => hne (Subtype.ext h)), pow_zero]
  have hvd : vd h M'' 𝔭 = vd h M 𝔭 + mu 𝔭 J := by
    rw [BrA.vd_eq hF hs M'', BrA.vd_eq hF hs M, hJ]
    exact mu_mul h𝔭 hD hJ0
  rw [hvd, pow_add, ← hJn', hJn, mul_comm]

end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

private theorem isLattice_inf_locF_of_isLattice {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (M ⊓ locF 𝔭 N) := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM hN
  have h0 : 𝔭 ≠ ⊥ := fun h0 =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h0 ▸ h𝔭))
  have hne : 𝔭 ^ r ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot] at h0 ⊢
    exact pow_ne_zero r h0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set c : K := algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) with hc_def
  have hc : c ≠ 0 := by
    intro hc0
    apply ha0
    apply NumberField.RingOfIntegers.algebraMap.injective F K
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    simpa [hc_def] using hc0
  refine ⟨?_, ?_⟩
  · have := hM
    have : IsNoetherian (𝓞 K) ↥(M ⊓ locF 𝔭 N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  · rw [eq_top_iff, ← hM.2, Submodule.span_le]
    intro y hy
    have hmem : algebraMap (𝓞 F) (𝓞 K) a • y ∈ M ⊓ locF 𝔭 N := ⟨M.smul_mem _ hy, hr a ha y hy⟩
    have ey : y = c⁻¹ • (algebraMap (𝓞 F) (𝓞 K) a • y) := by
      rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a) y, ← hc_def, smul_smul, inv_mul_cancel₀ hc,
        one_smul]
    rw [SetLike.mem_coe, ey]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  obtain ⟨r₁, hr₁⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  obtain ⟨r₂, hr₂⟩ := IA.exists_pow_smul h𝔭 hM₂ hM₁
  have e₁ := IA.card_eq_relIndex h𝔭 hr₁
  have e₂ := IA.card_eq_relIndex h𝔭 hr₂
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂

  have hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₁ ⊓ locF 𝔭 M₂) := fun x hx y hy => hM₁i x hx.1 y hy.1
  have hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₂ ⊓ locF 𝔭 M₁) := fun x hx y hy => hM₂i x hx.1 y hy.1
  have hvA := vd_locF hK hF hs hd (isLattice_inf_locF_of_isLattice h𝔭 hM₁ hM₂) hAi h𝔭
  have hvB := vd_locF hK hF hs hd (isLattice_inf_locF_of_isLattice h𝔭 hM₂ hM₁) hBi h𝔭
  rw [IA.locF_inf 𝔭 h𝔭.isPrime] at hvA hvB
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← hvA, ← hvB, inf_comm]
  rw [e₁, e₂, vd_locF hK hF hs hd hM₁ hM₁i h𝔭, vd_locF hK hF hs hd hM₂ hM₂i h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCC

open WCA WCB

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (han : ∀ x, h x x = 0 → x = 0) {A : Submodule (𝓞 K) V} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {v : ℕ} (hv : n ∉ 𝔭 ^ (v + 1))
    {x y : V} (hx : InL 𝔭 A 0 x) (hxx : h x x = κ (ι n)) (hyy : h y y = κ (ι n)) {J : ℕ}
    (hJ : 1 ≤ J) (hw : InL 𝔭 A (v + (v + J)) (y - x)) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ z, InL 𝔭 A 0 z → InL 𝔭 A J (g z - z)) ∧
      (∀ z, InL 𝔭 A 0 z → InL 𝔭 A 0 (g.symm z)) ∧ g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨θ₀, hθ₀⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := idealPowerSpanBounds.exists_inv_theta (K := K) hθ₀ 1
  have hconj : κ (conjO K θ₀) = star (κ θ₀) := rfl
  set δ : K := κ θ₀ - star (κ θ₀) with hδ
  have hδe : InI 𝔭 1 (δ * κ e - 1) := by
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), _, he, ?_⟩
    simp [hδ, hconj]
  obtain ⟨hne, hinv⟩ := InI.unit h𝔭 hF hδe
  have hδe' : 1 + (δ * κ e - 1) = δ * κ e := by ring
  rw [hδe'] at hne hinv
  have hδ0 : δ ≠ 0 := left_ne_zero_of_mul hne
  have he0 : κ e ≠ 0 := right_ne_zero_of_mul hne
  have hstarδ : star δ = -δ := by
    rw [hδ, star_sub, star_star]
    ring
  set l : K := κ θ₀ * δ⁻¹ with hl_def
  have hl : l + star l = 1 := by
    have h1 : l + star l = (κ θ₀ - star (κ θ₀)) * δ⁻¹ := by
      rw [hl_def, star_mul', star_inv₀, hstarδ, inv_neg]
      ring
    rw [h1]
    exact mul_inv_cancel₀ hδ0
  have hl0 : InI 𝔭 0 l := by
    have h1 := InI.mul hp (InI.int hp θ₀) (InI.mul hp (InI.int hp e) hinv)
    have h2 : κ e * (δ * κ e)⁻¹ = δ⁻¹ := by
      rw [mul_inv, mul_comm δ⁻¹, ← mul_assoc, mul_inv_cancel₀ he0, one_mul]
    rw [h2] at h1
    exact h1
  have hls0 : InI 𝔭 0 (star l) := InI.conj hF hl0
  set d : V := y - x with hd
  have hy : y = x + d := by simp [hd]
  have hexp : ∀ a b : V, h (a + b) (a + b) = h a a + h a b + h b a + h b b := by
    intro a b
    simp only [map_add, LinearMap.add_apply]
    ring
  have hdd : h x d + h d x + h d d = 0 := by
    have h1 := hexp x d
    rw [← hy, hyy, hxx] at h1
    linear_combination -h1
  set z₀ : V := x + star l • d with hz₀
  have hdL : InL 𝔭 A 0 (star l • d) := (InL.smul hp hls0 hw).mono (by omega)
  have hz₀L : InL 𝔭 A 0 z₀ := InL.add hp hx hdL
  have hsymm : ∀ a b : V, star (h a b) = h b a := fun a b => by
    simpa [starRingEnd_apply] using hs.eq a b
  set c : K := h z₀ z₀ with hc_def
  have hcstar : star c = c := hsymm z₀ z₀
  have hn0 : κ (ι n) ≠ 0 := κι_ne_zero hn
  have hcn : InI 𝔭 (v + (v + J)) (c - κ (ι n)) := by
    have h1 : c - κ (ι n) = h (star l • d) z₀ + h x (star l • d) := by
      rw [hc_def, hz₀]
      simp only [map_add, LinearMap.add_apply]
      rw [hxx]
      ring
    rw [h1]
    exact InI.add hp ((InL.form hp hF hA (InL.smul hp hls0 hw) hz₀L).mono (by omega))
      ((InL.form hp hF hA hx (InL.smul hp hls0 hw)).mono (by omega))
  set ε : K := (κ (ι n))⁻¹ * (c - κ (ι n)) with hε_def
  have hεv : InI 𝔭 (v + J) ε := InI.div h𝔭 hn hv hcn
  obtain ⟨hne', hinv'⟩ := InI.unit h𝔭 hF (hεv.mono (by omega))
  have hc : c = κ (ι n) * (1 + ε) := by
    rw [hε_def, mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    ring
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero hn0 hne'
  have hcinv : c⁻¹ = (1 + ε)⁻¹ * (κ (ι n))⁻¹ := by
    rw [hc, mul_inv, mul_comm]
  set w : V := c⁻¹ • d with hw_def
  have hwv : InL 𝔭 A (v + J) w := by
    rw [hw_def, hcinv, mul_smul]
    exact (InL.smul hp hinv' (InL.div h𝔭 hn hv hw)).mono (by omega)
  have hwJ : InL 𝔭 A J w := hwv.mono (by omega)
  have hw1 : InL 𝔭 A 1 w := hwv.mono (by omega)
  set θ : K := c⁻¹ * c⁻¹ * h d z₀ with hθ_def
  have hθJ : InI 𝔭 J θ := by
    have h1 : InI 𝔭 (v + (v + J)) (h d z₀) := (InL.form hp hF hA hw hz₀L).mono (by omega)
    have h2 := InI.div h𝔭 hn hv (InI.div h𝔭 hn hv h1)
    have h3 := InI.mul hp hinv' (InI.mul hp hinv' h2)
    have h4 : θ = (1 + ε)⁻¹ * ((1 + ε)⁻¹ *
        ((κ (ι n))⁻¹ * ((κ (ι n))⁻¹ * h d z₀))) := by
      rw [hθ_def, hcinv]
      ring
    rw [h4]
    exact h3.mono (by omega)
  have hθ1 : InI 𝔭 1 θ := hθJ.mono (by omega)
  have hskew : h d z₀ + h z₀ d = 0 := by
    rw [hz₀]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul,
      starRingEnd_apply, star_star]
    linear_combination hdd + h d d * hl
  have hθstar : star θ = -θ := by
    rw [hθ_def, star_mul', star_mul', star_inv₀, hcstar, hsymm]
    linear_combination c⁻¹ * c⁻¹ * hskew
  set Y : V →ₗ[K] V := WCB.skewY h z₀ w θ with hY_def
  have hY := WCB.skewY_skew hs z₀ w hθstar
  have hYz : Y z₀ = d := by
    rw [hY_def, WCB.skewY_apply]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    have hcoef : θ * c - h w z₀ = 0 := by
      rw [hw_def, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_inv₀,
        hcstar, smul_eq_mul, hθ_def]
      linear_combination c⁻¹ * h d z₀ * hcc
    rw [hcoef, zero_smul, zero_add, hw_def, smul_smul, hcc, one_smul]
  obtain ⟨g, hg, hgz, hs1, hs2⟩ := WCB.exists_cayley han hY hl
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z', hz'⟩ := hs1 z
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 hls0 hz hz'
    rw [← hz', hgz]
    have h1 : z' + l • Y z' - (z' - star l • Y z') = (l + star l) • Y z' := by
      rw [add_smul]
      abel
    rw [h1, hl, one_smul]
    exact WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L
  · intro z hz
    obtain ⟨z', hz'⟩ := hs2 z
    have hz'' : z' - (-l) • Y z' = z := by
      rw [neg_smul, sub_neg_eq_add]
      exact hz'
    have hz'L := WCB.mem_of_resolvent h𝔭 hF hA hz₀L hw1 hθ1 (InI.neg hl0) hz hz''
    have hgs : g.symm z = z' - star l • Y z' := by
      rw [LinearEquiv.symm_apply_eq, hgz, hz']
    rw [hgs]
    exact InL.sub hp hz'L ((InL.smul hp hls0 (WCB.skewY_mem hp hF hA hz₀L hwJ hθJ hz'L)).mono
      (by omega))
  · have hx' : z₀ - star l • Y z₀ = x := by
      rw [hYz, hz₀]
      abel
    rw [← hx', hgz, hYz, hz₀, hy, add_assoc, ← add_smul, add_comm (star l) l, hl, one_smul]

end Formalism.HermitianLattices.Ext.L3.WCC
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x y : V} (hxL : x ∈ (locF 𝔭 A₀))
    (hyL : y ∈ (locF 𝔭 A₀)) (hx : h x x = algebraMap F K (n : F)) (hy : h y y = algebraMap F K (n : F))
    {j : ℕ} (hj : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ j)
    (hxy : y - x ∈ ((extP K 𝔭) ^ j • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) :
    ∃ g ∈ autSub h (locF 𝔭 A₀),
      (∀ z ∈ (locF 𝔭 A₀), g z - z ∈ ((extP K 𝔭) ^ (j - 2 * vF 𝔭 n) • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) ∧
      g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have han : ∀ z, h z z = 0 → z = 0 := by
    intro z hz
    by_contra hz0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hpos := hd z hz0 φ
    rw [hz, map_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  set v := vF 𝔭 n with hvdef
  have hv : n ∉ 𝔭 ^ (v + 1) := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hx0 : WCA.InL 𝔭 A₀ 0 x := (WCA.inL_zero_iff hp).2 hxL
  have hJ : 1 ≤ j - 2 * v := by omega
  have hw : WCA.InL 𝔭 A₀ (v + (v + (j - 2 * v))) (y - x) := by
    have e : v + (v + (j - 2 * v)) = j := by omega
    rw [e]
    exact WCA.InL.of_mem h𝔭 hxy
  obtain ⟨g, hgI, hgJ, hgS, hgxy⟩ := WCC.core hK hF hs han hA₀i h𝔭 hn hv hx0 hx hy hJ hw
  have hL : ∀ z, z ∈ locF 𝔭 A₀ → g z ∈ locF 𝔭 A₀ := by
    intro z hz
    have hz0 : WCA.InL 𝔭 A₀ 0 z := (WCA.inL_zero_iff hp).2 hz
    have h1 : WCA.InL 𝔭 A₀ 0 (g z - z) := (hgJ z hz0).mono (Nat.zero_le _)
    have h2 := h1.add hp hz0
    rw [sub_add_cancel] at h2
    exact (WCA.inL_zero_iff hp).1 h2
  have hLs : ∀ z, z ∈ locF 𝔭 A₀ → g.symm z ∈ locF 𝔭 A₀ := fun z hz =>
    (WCA.inL_zero_iff hp).1 (hgS z ((WCA.inL_zero_iff hp).2 hz))
  refine ⟨g, ?_, fun z hz => (hgJ z ((WCA.inL_zero_iff hp).2 hz)).mem hp, hgxy⟩
  show g ∈ Formalism.ThetaLiftIndependence.autL h (locF 𝔭 A₀)
  refine ⟨hgI, le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hL z hz
  · intro z hz
    exact Submodule.mem_map.2 ⟨g.symm z, hLs z hz, by simp⟩

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace DA

theorem one_app (x : V) : (1 : V ≃ₗ[K] V) x = x := rfl

theorem apply_mem_smul {g : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hg : Formalism.HermitianLatticesTheory.gmap g A = A)
    (I : Ideal (𝓞 K)) {z : V} (hz : z ∈ (I • A : Submodule (𝓞 K) V)) :
    g z ∈ (I • A : Submodule (𝓞 K) V) := by
  have h1 : g z ∈ (I • A : Submodule (𝓞 K) V).map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    Submodule.mem_map_of_mem hz
  rw [Submodule.map_smul''] at h1
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg
  rwa [h2] at h1

theorem apply_mem {g : V ≃ₗ[K] V} {A : Submodule (𝓞 K) V} (hg : Formalism.HermitianLatticesTheory.gmap g A = A)
    {z : V} (hz : z ∈ A) : g z ∈ A := by
  have h1 : g z ∈ A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := Submodule.mem_map_of_mem hz
  have h2 : A.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) = A := hg
  rwa [h2] at h1

theorem mem_smul_top_iff (A : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (w : ↥A) :
    w ∈ (I • ⊤ : Submodule (𝓞 K) ↥A) ↔ (w : V) ∈ (I • A : Submodule (𝓞 K) V) := by
  have e : (I • ⊤ : Submodule (𝓞 K) ↥A).map A.subtype = I • A := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← e]
  constructor
  · intro hw
    exact Submodule.mem_map_of_mem hw
  · rintro ⟨w', hw', e'⟩
    rwa [← Subtype.ext (a1 := w') (a2 := w) e']

end DA

def stabB (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ autSub h A ∧ g x - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V)}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (a * b) x - x = a (b x - x) + (a x - x) := by
      rw [LinearEquiv.mul_apply, map_sub]
      abel
    rw [e]
    exact add_mem (DA.apply_mem_smul ha.2 _ hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : a⁻¹ x - x = -(a⁻¹ (a x - x)) := by
      rw [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app]
      abel
    rw [e]
    exact neg_mem (DA.apply_mem_smul (inv_mem ha).2 _ ha')

theorem mem_stabB {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x : V}
    {g : V ≃ₗ[K] V} : g ∈ stabB h A 𝔭 J x ↔
      g ∈ autSub h A ∧ g x - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := Iff.rfl

theorem mem_tube_bot {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x y : V} :
    y ∈ tube ⊥ A 𝔭 J x ↔ y - x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  constructor
  · rintro ⟨g, hg, hy⟩
    rw [Subgroup.mem_bot] at hg
    rwa [hg, DA.one_app] at hy
  · intro hy
    exact ⟨1, one_mem _, by rwa [DA.one_app]⟩

theorem quot_eq_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x : V}
    {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h A) (a b : ↥D) :
    (QuotientGroup.mk a : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) = QuotientGroup.mk b ↔
      (b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_stabB]
  have ha := hD a.2
  have hb := hD b.2
  have e1 : ((a⁻¹ * b : ↥D) : V ≃ₗ[K] V) x - x =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x) := by
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, inv_mul_cancel,
      DA.one_app]
    rfl
  constructor
  · rintro ⟨-, h2⟩
    rw [e1] at h2
    have := DA.apply_mem_smul ha.2 _ h2
    rwa [← LinearEquiv.mul_apply, mul_inv_cancel, DA.one_app] at this
  · intro h2
    refine ⟨hD (a⁻¹ * b).2, ?_⟩
    rw [e1]
    exact DA.apply_mem_smul (inv_mem ha).2 _ h2

theorem cnt_tube_eq {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (n : 𝓞 F) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    {J k : ℕ} (hJk : J ≤ k) {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h (locF 𝔭 A₀)) :
    cnt h (locF 𝔭 A₀) 𝔭 k n (tube D (locF 𝔭 A₀) 𝔭 J x) =
      (stabB h (locF 𝔭 A₀) 𝔭 J x).relIndex D * cnt h (locF 𝔭 A₀) 𝔭 k n (tube ⊥ (locF 𝔭 A₀) 𝔭 J x) := by
  classical
  set A := locF 𝔭 A₀ with hA
  have hfinJ : Finite (↥A ⧸ ((extP K 𝔭) ^ J • ⊤ : Submodule (𝓞 K) ↥A)) := finite_quot hA₀ h𝔭 J
  have hfink : Finite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) := finite_quot hA₀ h𝔭 k

  let φ : ↥D → ↥A ⧸ ((extP K 𝔭) ^ J • ⊤ : Submodule (𝓞 K) ↥A) := fun g =>
    Submodule.Quotient.mk ⟨(g : V ≃ₗ[K] V) x, DA.apply_mem (hD g.2).2 hxA⟩
  have hφ : ∀ a b : ↥D, φ a = φ b ↔
      (QuotientGroup.mk a : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) = QuotientGroup.mk b := by
    intro a b
    rw [quot_eq_iff hD, eq_comm, Submodule.Quotient.eq, DA.mem_smul_top_iff]
    rfl
  have hfinQ : Finite (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) := by
    refine Finite.of_injective (Quotient.lift φ ?_) ?_
    · intro a b hab
      exact (hφ a b).mpr (Quotient.sound hab)
    · intro a b
      induction a using Quotient.inductionOn with | _ a => ?_
      induction b using Quotient.inductionOn with | _ b => ?_
      intro e
      exact (hφ a b).mp e
  have := Fintype.ofFinite (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D)
  let Ω : (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) → Set V := fun c =>
    tube ⊥ A 𝔭 J (((Quotient.out c : ↥D) : V ≃ₗ[K] V) x)
  have hU : tube D A 𝔭 J x = ⋃ c ∈ (Finset.univ : Finset (↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D)), Ω c := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨g, hg, hy⟩
      refine ⟨QuotientGroup.mk (⟨g, hg⟩ : ↥D), ?_⟩
      rw [mem_tube_bot]
      have h1 := (quot_eq_iff (𝔭 := 𝔭) (J := J) (x := x) hD
        (Quotient.out (QuotientGroup.mk (⟨g, hg⟩ : ↥D) : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D))
        ⟨g, hg⟩).mp (Quotient.out_eq _)
      have := add_mem hy h1
      rwa [sub_add_sub_cancel] at this
    · rintro ⟨c, hc⟩
      exact ⟨_, (Quotient.out c : ↥D).2, mem_tube_bot.mp hc⟩
  rw [hU, cnt_biUnion h A 𝔭 k n hfink]
  · have hterm : ∀ c, cnt h A 𝔭 k n (Ω c) = cnt h A 𝔭 k n (tube ⊥ A 𝔭 J x) := by
      intro c
      have hg := hD (Quotient.out c : ↥D).2
      have h1 := cnt_gmap hg.1 A 𝔭 k n (tube ⊥ A 𝔭 J x)
      rw [hg.2] at h1
      rw [← h1]
      congr 1
      ext y
      rw [mem_tube_bot]
      constructor
      · intro hy
        refine ⟨((Quotient.out c : ↥D) : V ≃ₗ[K] V)⁻¹ y, ?_, ?_⟩
        · rw [mem_tube_bot]
          have := DA.apply_mem_smul (inv_mem hg).2 _ hy
          rwa [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app] at this
        · rw [← LinearEquiv.mul_apply, mul_inv_cancel, DA.one_app]
      · rintro ⟨z, hz, rfl⟩
        rw [← map_sub]
        exact DA.apply_mem_smul hg.2 _ (mem_tube_bot.mp hz)
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card]
    rfl
  · intro c _ y hy z hz
    rw [mem_tube_bot] at hy ⊢
    rw [add_sub_right_comm]
    exact add_mem hy (pow_smul_anti 𝔭 A hJk hz)
  · intro c _ c' _ hne
    rw [Set.disjoint_left]
    intro y hy hy'
    apply hne
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    refine (quot_eq_iff (𝔭 := 𝔭) (J := J) (x := x) hD _ _).mpr ?_
    have := sub_mem (mem_tube_bot.mp hy) (mem_tube_bot.mp hy')
    rwa [sub_sub_sub_cancel_left] at this

theorem cnt_tube_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    (hx : h x x = algebraMap F K (n : F))
    {J k : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ J) (hJk : J ≤ k)
    {C : Subgroup (V ≃ₗ[K] V)} (hC : C ≤ autSub h (locF 𝔭 A₀))
    (hΓ : ∀ g ∈ autSub h (locF 𝔭 A₀), (∀ z ∈ locF 𝔭 A₀,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • locF 𝔭 A₀ : Submodule (𝓞 K) V)) → g ∈ C) :
    cnt h (locF 𝔭 A₀) 𝔭 k n (tube (autSub h (locF 𝔭 A₀)) (locF 𝔭 A₀) 𝔭 J x) *
        C.relIndex (autSub h (locF 𝔭 A₀) ⊓ fixS x) =
      C.relIndex (autSub h (locF 𝔭 A₀)) * cnt h (locF 𝔭 A₀) 𝔭 k n (tube C (locF 𝔭 A₀) 𝔭 J x) := by
  set A := locF 𝔭 A₀ with hA
  have hidx := index_tube (autSub h A) (stabB h A 𝔭 J x) C (autSub h A ⊓ fixS x)
    (fun g hg => hg.1) hC
    (by
      rintro g ⟨hg, hgx⟩
      refine ⟨hg, ?_⟩
      rw [mem_fixS.mp hgx, sub_self]
      exact zero_mem _)
    (by
      rintro s ⟨hs1, hs2⟩
      have hsi := inv_mem hs1
      have hx' : h (s⁻¹ x) (s⁻¹ x) = algebraMap F K (n : F) := by rw [hsi.1, hx]
      have hd' : x - s⁻¹ x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
        have := DA.apply_mem_smul hsi.2 _ hs2
        rwa [map_sub, ← LinearEquiv.mul_apply, inv_mul_cancel, DA.one_app] at this
      obtain ⟨γ, hγ1, hγ2, hγ3⟩ := exists_isom_congr hK hF hs hd hA₀ hA₀i h𝔭 hn
        (DA.apply_mem hsi.2 hxA) hxA hx' hx hJ hd'
      refine ⟨γ * s⁻¹, ⟨mul_mem hγ1 hsi, ?_⟩, ?_⟩
      · change (γ * s⁻¹) x = x
        rw [LinearEquiv.mul_apply, hγ3]
      · rw [inv_mul_cancel_right]
        exact hΓ γ hγ1 hγ2)
  rw [cnt_tube_eq hA₀ h𝔭 n hxA hJk le_rfl, cnt_tube_eq hA₀ h𝔭 n hxA hJk hC, mul_right_comm, hidx,
    mul_assoc]

theorem cnt_tube_refine (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x : V} (hxA : x ∈ locF 𝔭 A₀)
    (hx : h x x = algebraMap F K (n : F))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ J)
    {C : Subgroup (V ≃ₗ[K] V)} (hC : C ≤ autSub h (locF 𝔭 A₀))
    (hΓ : ∀ g ∈ autSub h (locF 𝔭 A₀), (∀ z ∈ locF 𝔭 A₀,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • locF 𝔭 A₀ : Submodule (𝓞 K) V)) → g ∈ C)
    {B : Submodule (𝓞 K) V} (hBA : B ≤ locF 𝔭 A₀) {r : ℕ}
    (hr : ((extP K 𝔭) ^ r • locF 𝔭 A₀ : Submodule (𝓞 K) V) ≤ B) {J₂ : ℕ} (hJ₂ : J ≤ J₂) :
    ∀ᶠ k in atTop, cnt h (locF 𝔭 A₀) 𝔭 k n (tube C (locF 𝔭 A₀) 𝔭 J x) =
      cnt h (locF 𝔭 A₀) 𝔭 k n (tube C B 𝔭 J₂ x) := by
  set A := locF 𝔭 A₀ with hA
  obtain ⟨c₀, hc₀⟩ := exists_exact_near hK hF hs hd hA₀ hA₀i h𝔭 hn ⟨x, hx⟩
  filter_upwards [eventually_ge_atTop (c₀ + (J₂ + r))] with k hk
  refine cnt_congr h A 𝔭 k n fun y hy hyn => ⟨?_, ?_⟩
  · rintro ⟨c, hc, hyc⟩
    obtain ⟨x', hx'A, hx', hx'y⟩ := hc₀ k (by omega) y hy hyn
    have hcA := hC hc
    have h1 : x' - c x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
      have := add_mem (pow_smul_anti 𝔭 A (show J ≤ k - c₀ by omega) hx'y) hyc
      rwa [sub_add_sub_cancel] at this
    obtain ⟨γ, hγ1, hγ2, hγ3⟩ := exists_isom_congr hK hF hs hd hA₀ hA₀i h𝔭 hn
      (DA.apply_mem hcA.2 hxA) hx'A (by rw [hcA.1, hx]) hx' hJ h1
    refine ⟨γ * c, mul_mem (hΓ γ hγ1 hγ2) hc, ?_⟩
    rw [LinearEquiv.mul_apply, hγ3, ← neg_sub]
    apply neg_mem
    have h2 := pow_smul_anti 𝔭 A (show J₂ + r ≤ k - c₀ by omega) hx'y
    rw [pow_add, mul_smul] at h2
    exact Submodule.smul_mono le_rfl hr h2
  · rintro ⟨c, hc, hyc⟩
    exact ⟨c, hc, pow_smul_anti 𝔭 A hJ₂ (Submodule.smul_mono le_rfl hBA hyc)⟩

theorem pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) {x : V} (hx : h x x = algebraMap F K (n : F)) (hx₁ : x ∈ locF 𝔭 M₁)
    (hx₂ : x ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      cnt h (locF 𝔭 M₁) 𝔭 k n (tube (autSub h (locF 𝔭 M₁)) (locF 𝔭 M₁) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 *
          (autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) *
          (autSub h (locF 𝔭 M₂) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₁) ⊓ fixS x) =
        cnt h (locF 𝔭 M₂) 𝔭 k n (tube (autSub h (locF 𝔭 M₂)) (locF 𝔭 M₂) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 *
          (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) *
          (autSub h (locF 𝔭 M₁) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₂) ⊓ fixS x) := by
  set A₁ := locF 𝔭 M₁ with hA₁
  set A₂ := locF 𝔭 M₂ with hA₂
  set C := autSub h A₁ ⊓ autSub h A₂ with hC
  set B := A₁ ⊓ A₂ with hB
  obtain ⟨j₁, hj₁⟩ := exists_congr_mem_autSub h hM₁ hM₂ h𝔭
  obtain ⟨j₂, hj₂⟩ := exists_congr_mem_autSub h hM₂ hM₁ h𝔭
  obtain ⟨r₁, hr₁⟩ := exists_pow_smul_le hM₁ hM₂ h𝔭
  obtain ⟨r₂, hr₂⟩ := exists_pow_smul_le hM₂ hM₁ h𝔭
  have hr₁' : ((extP K 𝔭) ^ r₁ • A₁ : Submodule (𝓞 K) V) ≤ B := le_inf Submodule.smul_le_right hr₁
  have hr₂' : ((extP K 𝔭) ^ r₂ • A₂ : Submodule (𝓞 K) V) ≤ B := le_inf hr₂ Submodule.smul_le_right
  have hlA₁ : locF 𝔭 A₁ = A₁ := LocalizedFibreSets.locF_idem 𝔭 M₁
  have hlA₂ : locF 𝔭 A₂ = A₂ := LocalizedFibreSets.locF_idem 𝔭 M₂
  have hlB : locF 𝔭 B = B := locF_inf h𝔭 hlA₁ hlA₂
  have hCB : ∀ g ∈ C, Formalism.HermitianLatticesTheory.gmap g B = B := by
    rintro g ⟨hg1, hg2⟩
    have e : Formalism.HermitianLatticesTheory.gmap g B = Formalism.HermitianLatticesTheory.gmap g A₁ ⊓ Formalism.HermitianLatticesTheory.gmap g A₂ :=
      Submodule.map_inf _ g.injective
    rw [e, hg1.2, hg2.2]
  filter_upwards [eventually_ge_atTop (4 * vF 𝔭 n + eA h A₁ 𝔭 + 1 + (4 * vF 𝔭 n + eA h A₂ 𝔭 + 1) +
    (j₁ + j₂ + 2 * vF 𝔭 n))] with J hJ
  have hJ₁ : 4 * vF 𝔭 n + eA h A₁ 𝔭 + 1 ≤ J := by omega
  have hJ₂ : 4 * vF 𝔭 n + eA h A₂ 𝔭 + 1 ≤ J := by omega
  have hΓ₁ : ∀ g ∈ autSub h A₁, (∀ z ∈ A₁,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • A₁ : Submodule (𝓞 K) V)) → g ∈ C :=
    fun g hg hz => ⟨hg, hj₁ _ (by omega) g hg hz⟩
  have hΓ₂ : ∀ g ∈ autSub h A₂, (∀ z ∈ A₂,
      g z - z ∈ ((extP K 𝔭) ^ (J - 2 * vF 𝔭 n) • A₂ : Submodule (𝓞 K) V)) → g ∈ C :=
    fun g hg hz => ⟨hj₂ _ (by omega) g hg hz, hg⟩
  filter_upwards [cnt_tube_refine hK hF hs hd hM₁ hM₁i h𝔭 hn hx₁ hx (J := J) hJ₁
      (C := C) inf_le_left hΓ₁ (B := B) inf_le_left hr₁' (le_refl J),
    cnt_tube_refine hK hF hs hd hM₂ hM₂i h𝔭 hn hx₂ hx (J := J) hJ₂
      (C := C) inf_le_right hΓ₂ (B := B) inf_le_right hr₂' (le_refl J),
    eventually_ge_atTop (J + r₁ + r₂)] with k hk₁ hk₂ hk
  have m₁ := cnt_tube_mul hK hF hs hd hM₁ hM₁i h𝔭 hn hx₁ hx (J := J) (k := k) hJ₁ (by omega)
    (C := C) inf_le_left hΓ₁
  have m₂ := cnt_tube_mul hK hF hs hd hM₂ hM₂i h𝔭 hn hx₂ hx (J := J) (k := k) hJ₂ (by omega)
    (C := C) inf_le_right hΓ₂
  rw [← hA₁] at m₁ hk₁
  rw [← hA₂] at m₂ hk₂
  rw [hk₁] at m₁
  rw [hk₂] at m₂

  have hΩB : tube C B 𝔭 J x ⊆ B := by
    rintro y ⟨g, hg, hy⟩
    have h1 : g x ∈ B := DA.apply_mem (hCB g hg) ⟨hx₁, hx₂⟩
    have := add_mem (Submodule.smul_le_right hy) h1
    rwa [sub_add_cancel] at this
  have hst : ∀ (A : Submodule (𝓞 K) V) (r : ℕ), ((extP K 𝔭) ^ r • A : Submodule (𝓞 K) V) ≤ B →
      J + r ≤ k → ∀ y ∈ tube C B 𝔭 J x, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V),
        y + z ∈ tube C B 𝔭 J x := by
    rintro A r hr hrk y ⟨g, hg, hy⟩ z hz
    refine ⟨g, hg, ?_⟩
    rw [add_sub_right_comm]
    refine add_mem hy ?_
    have h2 := pow_smul_anti 𝔭 A hrk hz
    rw [pow_add, mul_smul] at h2
    exact Submodule.smul_mono le_rfl hr h2
  have hle : ∀ (A : Submodule (𝓞 K) V) (r : ℕ), ((extP K 𝔭) ^ r • A : Submodule (𝓞 K) V) ≤ B →
      r ≤ k → ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ≤ B :=
    fun A r hr hrk => (pow_smul_anti 𝔭 A hrk).trans hr
  have hfinB := finite_quot_inf hM₁ hM₂ h𝔭 k
  have s₁ := cnt_sub hF (h := h) h𝔭 hlA₁ hlB (GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hM₁i) inf_le_left
    (hle A₁ r₁ hr₁' (by omega)) hfinB n hΩB (hst A₁ r₁ hr₁' (by omega))
  have s₂ := cnt_sub hF (h := h) h𝔭 hlA₂ hlB (GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hM₂i) inf_le_right
    (hle A₂ r₂ hr₂' (by omega)) hfinB n hΩB (hst A₂ r₂ hr₂' (by omega))
  have i0 := card_quot_inf_ne_zero hM₁ hM₂ h𝔭
  have im := card_quot_inf_mul hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭
  rw [← hA₁, ← hA₂, ← hB] at i0 im
  have hq : Ideal.absNorm 𝔭 ≠ 0 := (reductionMapsOfForms.absNorm_pos h𝔭).ne'

  have e1 : C.relIndex (autSub h A₁) = (autSub h A₂).relIndex (autSub h A₁) := by
    rw [hC, Subgroup.inf_relIndex_left]
  have e2 : C.relIndex (autSub h A₂) = (autSub h A₁).relIndex (autSub h A₂) := by
    rw [hC, Subgroup.inf_relIndex_right]
  have e3 : C.relIndex (autSub h A₁ ⊓ fixS x) =
      (autSub h A₂ ⊓ fixS x).relIndex (autSub h A₁ ⊓ fixS x) := by
    rw [← Subgroup.inf_relIndex_right C, ← Subgroup.inf_relIndex_right (autSub h A₂ ⊓ fixS x)]
    congr 1
    rw [hC]
    ac_rfl
  have e4 : C.relIndex (autSub h A₂ ⊓ fixS x) =
      (autSub h A₁ ⊓ fixS x).relIndex (autSub h A₂ ⊓ fixS x) := by
    rw [← Subgroup.inf_relIndex_right C, ← Subgroup.inf_relIndex_right (autSub h A₁ ⊓ fixS x)]
    congr 1
    rw [hC]
    ac_rfl
  rw [e1, e3] at m₁
  rw [e2, e4] at m₂
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero i0 (pow_ne_zero (vd h A₁ 𝔭) hq)))
  generalize cnt h A₁ 𝔭 k n (tube (autSub h A₁) A₁ 𝔭 J x) = E₁ at *
  generalize cnt h A₂ 𝔭 k n (tube (autSub h A₂) A₂ 𝔭 J x) = E₂ at *
  generalize cnt h A₁ 𝔭 k n (tube C B 𝔭 J x) = D₁ at *
  generalize cnt h A₂ 𝔭 k n (tube C B 𝔭 J x) = D₂ at *
  generalize cnt h B 𝔭 k n (tube C B 𝔭 J x) = W at *
  generalize Nat.card (↥A₁ ⧸ B.submoduleOf A₁) = i₁ at *
  generalize Nat.card (↥A₂ ⧸ B.submoduleOf A₂) = i₂ at *
  generalize Ideal.absNorm 𝔭 ^ vd h A₁ 𝔭 = Q₁ at *
  generalize Ideal.absNorm 𝔭 ^ vd h A₂ 𝔭 = Q₂ at *
  generalize (autSub h A₂).relIndex (autSub h A₁) = a at *
  generalize (autSub h A₁).relIndex (autSub h A₂) = b at *
  generalize (autSub h A₂ ⊓ fixS x).relIndex (autSub h A₁ ⊓ fixS x) = a' at *
  generalize (autSub h A₁ ⊓ fixS x).relIndex (autSub h A₂ ⊓ fixS x) = b' at *
  calc i₁ * Q₁ * (E₁ * Q₂ * b * a') = (E₁ * a') * i₁ * Q₁ * Q₂ * b := by ring
    _ = a * (i₁ * D₁) * Q₁ * Q₂ * b := by rw [m₁]; ring
    _ = a * (i₂ * D₂) * Q₁ * Q₂ * b := by rw [← s₁, s₂]
    _ = (b * D₂) * a * Q₁ * (i₂ * Q₂) := by ring
    _ = (E₂ * b') * a * Q₁ * (i₁ * Q₁) := by rw [← m₂, ← im]
    _ = i₁ * Q₁ * (E₂ * Q₁ * a * b') := by ring

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end
