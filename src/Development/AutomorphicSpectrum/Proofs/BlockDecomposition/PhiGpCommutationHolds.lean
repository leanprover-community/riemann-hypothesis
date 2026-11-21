import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomy
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeFunctorTwistEquiv

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_cInd_restrict : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  intro G G' W W' _ _ _ _ _ _ _ _ _ _ H H' ι σ σ' q hι hH hq hS hemb hcomp f
  obtain ⟨K', hK'n, hK'c⟩ := hcomp
  obtain ⟨L, hLo, hL⟩ := cInd_right_inv H σ f
  let b : G' → W' := fun x => q (f.1.1.1 (ι x))
  have hind : b ∈ indSpace H' σ' := by
    intro h x
    have hh : ι (h : G') ∈ H := (hH _).1 h.2
    have e : f.1.1.1 (((⟨ι h, hh⟩ : H) : G) * ι x) = σ ⟨ι h, hh⟩ (f.1.1.1 (ι x)) := f.1.1.2 ⟨ι h, hh⟩ (ι x)
    show q (f.1.1.1 (ι ((h : G') * x))) = σ' h (q (f.1.1.1 (ι x)))
    rw [map_mul, ← hq h hh]
    exact congrArg q e
  have hsm : (⟨b, hind⟩ : indSpace H' σ') ∈ smoothPart (ind H' σ') := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H' σ') (L.comap ι)
      (hLo.preimage hι) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show q (f.1.1.1 (ι (g * x))) = q (f.1.1.1 (ι g))
    rw [map_mul, hL (ι g) (ι x) hx]
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H' σ')) ∈ cIndSpace H' σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    have hD : IsCompact (C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}) := hC.inter_right hS
    have key : ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H,
        ∀ n ∈ C ∩ {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x}, ι x = a * n →
        ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c' := by
      refine hD.induction_on
        (p := fun A => ∃ C' : Set G', IsCompact C' ∧ ∀ (x : G'), ∀ a ∈ H, ∀ n ∈ A, ι x = a * n →
          ∃ h' ∈ H', ∃ c' ∈ C', x = h' * c') ?_ ?_ ?_ ?_
      · exact ⟨∅, isCompact_empty, fun _ _ _ n hn => absurd hn (Set.notMem_empty n)⟩
      · rintro A B hAB ⟨C', hC', h⟩
        exact ⟨C', hC', fun x a ha n hn e => h x a ha n (hAB hn) e⟩
      · rintro A B ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
        refine ⟨C₁ ∪ C₂, hC₁.union hC₂, fun x a ha n hn e => ?_⟩
        rcases hn with hn | hn
        · obtain ⟨h', hh', c', hc', e'⟩ := h₁ x a ha n hn e
          exact ⟨h', hh', c', Or.inl hc', e'⟩
        · obtain ⟨h', hh', c', hc', e'⟩ := h₂ x a ha n hn e
          exact ⟨h', hh', c', Or.inr hc', e'⟩
      · rintro c ⟨-, h₀, hh₀, s, rfl⟩
        obtain ⟨K, hK, hKe⟩ := hemb K' hK'n
        have hcont : Continuous fun n : G => h₀⁻¹ * n * (ι s)⁻¹ := by fun_prop
        have hN : (fun n : G => h₀⁻¹ * n * (ι s)⁻¹) ⁻¹' K ∈ 𝓝 (h₀ * ι s) := by
          apply hcont.continuousAt.preimage_mem_nhds
          have e : h₀⁻¹ * (h₀ * ι s) * (ι s)⁻¹ = 1 := by group
          rw [e]
          exact hK
        refine ⟨_, mem_nhdsWithin_of_mem_nhds hN, (fun y => y * s) '' K',
          hK'c.image (by fun_prop), fun x a ha n hn e => ?_⟩
        have hn' : h₀⁻¹ * n * (ι s)⁻¹ ∈ K := hn
        have e2 : ι (x * s⁻¹) = (a * h₀) * (h₀⁻¹ * n * (ι s)⁻¹) := by
          rw [map_mul, map_inv, e]
          group
        obtain ⟨h', hh', κ', hκ', e3⟩ := hKe _ _ (mul_mem ha hh₀) _ hn' e2
        refine ⟨h', hh', κ' * s, ⟨κ', hκ', rfl⟩, ?_⟩
        rw [← mul_assoc, ← e3]
        group
    obtain ⟨C', hC', hkey⟩ := key
    refine ⟨C', hC', fun x hx => ?_⟩
    have hne : f.1.1.1 (ι x) ≠ 0 := by
      intro h0
      apply hx
      show q (f.1.1.1 (ι x)) = 0
      rw [h0, map_zero]
    obtain ⟨a, ha, c, hcC, e⟩ := hf (ι x) hne
    refine hkey x a ha c ⟨hcC, a⁻¹, inv_mem ha, x, ?_⟩ e
    rw [e]
    group
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun x => rfl⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_map_intertwines_restriction : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x} →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∃ K' ∈ 𝓝 (1 : G'), IsCompact K') →
    ∀ f : cIndSpace H σ, ∃ F : cIndSpace H' σ', ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem cIndSpace_apply_mem_mul {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] {H : Subgroup G}
    {σ : Representation ℂ H W} (f : GlobalTheory.PRep.cIndSpace H σ) (h : G) (hh : h ∈ H)
    (g : G) : f.1.1.1 (h * g) = σ ⟨h, hh⟩ (f.1.1.1 g) := by
  exact f.1.1.2 ⟨h, hh⟩ g

private theorem isHK_empty {G : Type} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H ∅ := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK
  exact ⟨fun _ _ _ => Iff.rfl, ⊤, by simp, fun _ _ _ => Iff.rfl⟩

private theorem isHK_union {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A ∪ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_union, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_union, hA₂ g x hx.1, hB₂ g x hx.2]

private theorem isHK_diff {G : Type} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {A B : Set G} (hA : GlobalTheory.CompanionTheory.LeibPhi.IsHK H A)
    (hB : GlobalTheory.CompanionTheory.LeibPhi.IsHK H B) : GlobalTheory.CompanionTheory.LeibPhi.IsHK H (A \ B) := by
  unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at *
  obtain ⟨hA₁, KA, hKA, hA₂⟩ := hA
  obtain ⟨hB₁, KB, hKB, hB₂⟩ := hB
  refine ⟨fun h hh g => ?_, KA ⊓ KB, ?_, fun g x hx => ?_⟩
  · simp only [Set.mem_diff, hA₁ h hh g, hB₁ h hh g]
  · rw [Subgroup.coe_inf]
    exact hKA.inter hKB
  · rw [Subgroup.mem_inf] at hx
    simp only [Set.mem_diff, hA₂ g x hx.1, hB₂ g x hx.2]

theorem exists_cInd_restrict_eq {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W') (hι : Continuous ι) (hσ : IsSmooth σ) (hsurj : Function.Surjective q)
    (hH : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (F : cIndSpace H' σ') : ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  classical
  obtain ⟨C, hC, hsupp⟩ : ∃ C : Set G', IsCompact C ∧
      ∀ g, F.1.1.1 g ≠ 0 → ∃ h ∈ H', ∃ c ∈ C, g = h * c := F.2
  have hloc : ∀ c : G', ∃ T : Set G, ∃ U ∈ 𝓝 c, GlobalTheory.CompanionTheory.LeibPhi.IsHK H T ∧
      (∀ y ∈ U, ι y ∈ T) ∧ ∃ e : GlobalTheory.PRep.cIndSpace H σ,
        ∀ x, ι x ∈ T → q (e.1.1.1 (ι x)) = F.1.1.1 x := by
    intro c
    obtain ⟨K', hK'o, hK'⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H' σ' F
    obtain ⟨w, hw⟩ := hsurj (F.1.1.1 c)
    obtain ⟨e, he⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_value H σ hσ hbase (ι c) w
    obtain ⟨Ke, hKeo, hKe⟩ := GlobalTheory.CompanionTheory.LeibPhi.cInd_right_inv H σ e
    have hS : {y : G' | c⁻¹ * y * c ∈ K' ∧ ι (c⁻¹ * y * c) ∈ Ke} ∈ 𝓝 (1 : G') := by
      have hcont : Continuous (fun y : G' => c⁻¹ * y * c) := by fun_prop
      have hopen : IsOpen {z : G' | z ∈ K' ∧ ι z ∈ Ke} := hK'o.inter (hKeo.preimage hι)
      exact (hopen.preimage hcont).mem_nhds (by simp [one_mem])
    obtain ⟨K, hK, hKemb⟩ := hemb _ hS
    have hconj : (fun μ : G => ι c * μ * (ι c)⁻¹) ⁻¹' K ∈ 𝓝 (1 : G) := by
      have hcont : Continuous (fun μ : G => ι c * μ * (ι c)⁻¹) := by fun_prop
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    obtain ⟨M, hMo, -, hMsub⟩ := hbase _ hconj
    refine ⟨{g | ∃ a ∈ H, ∃ x ∈ M, g = a * ι c * x}, {y | ι (c⁻¹ * y) ∈ M}, ?_,
      GlobalTheory.CompanionTheory.LeibPhi.isHK_doubleCoset H M hMo (ι c), ?_, e, ?_⟩
    · have hcont : Continuous (fun y : G' => ι (c⁻¹ * y)) := hι.comp (continuous_mul_left c⁻¹)
      exact (hMo.preimage hcont).mem_nhds (by simp [one_mem])
    · intro y hy
      exact ⟨1, one_mem _, ι (c⁻¹ * y), hy, by simp⟩
    · rintro x ⟨a, ha, μ, hμ, hx⟩
      have hκ : ι c * μ * (ι c)⁻¹ ∈ K := hMsub hμ
      obtain ⟨h', hh', κ', hκ', hxeq⟩ := hKemb (x * c⁻¹) a ha (ι c * μ * (ι c)⁻¹) hκ
        (by rw [map_mul, hx, map_inv]; group)
      have hx' : x = h' * (c * (c⁻¹ * κ' * c)) := by
        have h0 : x = x * c⁻¹ * c := by group
        rw [h0, hxeq]
        group
      have hι' : ι h' ∈ H := (hH h').1 hh'
      have hFx : F.1.1.1 x = σ' ⟨h', hh'⟩ (q w) := by
        rw [hx', cIndSpace_apply_mem_mul F h' hh', hK' c _ hκ'.1, hw]
      rw [hFx, hx', map_mul, map_mul, cIndSpace_apply_mem_mul e _ hι',
        hKe _ _ hκ'.2, he]
      exact hq ⟨h', hh'⟩ hι' w
  choose T U hU hT hUT e he using hloc
  obtain ⟨t, -, hCt⟩ := hC.elim_nhds_subcover U (fun c _ => hU c)
  have hglue : ∀ s : Finset G', ∃ V : Set G, GlobalTheory.CompanionTheory.LeibPhi.IsHK H V ∧
      (∀ c ∈ s, T c ⊆ V) ∧ ∃ f : GlobalTheory.PRep.cIndSpace H σ,
        (∀ g ∉ V, f.1.1.1 g = 0) ∧ ∀ x, ι x ∈ V → q (f.1.1.1 (ι x)) = F.1.1.1 x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨∅, isHK_empty H, by simp, 0, fun g _ => ?_, fun x hx => ?_⟩
      · rfl
      · simp at hx
    | @insert c s hcs ih =>
      obtain ⟨V, hV, hsV, f, hf0, hf⟩ := ih
      obtain ⟨f', hf'in, hf'out⟩ := GlobalTheory.CompanionTheory.LeibPhi.exists_indicator H σ
        (isHK_diff (hT c) hV) (e c)
      have hadd : ∀ g, (f + f').1.1.1 g = f.1.1.1 g + f'.1.1.1 g := fun _ => rfl
      refine ⟨V ∪ T c, isHK_union hV (hT c), ?_, f + f', ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact Set.subset_union_right
        · exact (hsV d hd).trans Set.subset_union_left
      · intro g hg
        rw [Set.mem_union, not_or] at hg
        rw [hadd, hf0 g hg.1, hf'out g (fun h => hg.2 h.1), add_zero]
      · intro x hx
        by_cases hxV : ι x ∈ V
        · rw [hadd, hf'out _ (fun h => h.2 hxV), add_zero]
          exact hf x hxV
        · rcases hx with hx | hx
          · exact absurd hx hxV
          · rw [hadd, hf0 _ hxV, hf'in _ ⟨hx, hxV⟩, zero_add]
            exact he c x hx
  obtain ⟨V, hV, htV, f, hf0, hf⟩ := hglue t
  refine ⟨f, fun x => ?_⟩
  by_cases hx : ι x ∈ V
  · exact (hf x hx).symm
  · rw [hf0 _ hx, map_zero]
    by_contra hne
    obtain ⟨h', hh', c', hc', rfl⟩ := hsupp x hne
    obtain ⟨d, hd, hc'U⟩ := Set.mem_iUnion₂.1 (hCt hc')
    have hmem : ι c' ∈ V := htV d hd (hUT d c' hc'U)
    unfold GlobalTheory.CompanionTheory.LeibPhi.IsHK at hV
    apply hx
    rw [map_mul]
    exact (hV.1 _ ((hH h').1 hh') _).2 hmem

end GlobalTheory.CompanionTheory.LeibPhi
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_map_induced_surjective_intertwiner : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → IsSmooth σ → Function.Surjective q →
    (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ F : cIndSpace H' σ', ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, if_neg hc, if_neg hrc,
    add_zero]

theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) : MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  rw [GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff]
  intro b a
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  have ha := a.isLt
  apply one_add_colMat_apply_eq_zero_of_ne_last
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, Fin.val_last] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val, GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
    omega

end GlobalTheory.CompanionTheory.LeibPhi
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem gpProj_mirUin_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  intro k _ _ _ _ ψ m j u hh
  obtain ⟨h1, hv⟩ := GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k m (j + 1) ⟨u, hh⟩ u.2
  refine ⟨h1, hv, ?_⟩
  obtain ⟨w', hw'⟩ := id (id hv : (((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) ∈ MirU k (j + 1))
  obtain ⟨w, hw⟩ := (u.2 : ((u : Mir k (m + j + 1)) : GL (Fin (m + j + 1 + 1)) k) ∈ MirU k (m + j + 1))
  rw [mirChar_eq k ψ j ⟨_, hv⟩ w' hw'.symm, mirChar_eq k ψ (m + j) u w hw.symm]
  have hent : ((((gpProj k m (j + 1) ⟨u, hh⟩).2 : Mir k (j + 1)) : GL (Fin (j + 1 + 1)) k) : Matrix _ _ k)
      (Fin.castSucc (Fin.last j)) (Fin.last (j + 1)) =
      (((u : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k)
        (eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩) (eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩) := by
    show (leviProj k (eGP m (j + 1)) (hgpIncl k m (j + 1) ⟨u, hh⟩) true).val _ _ = _
    rw [leviProj_apply]
    rfl
  have e : eGP m (j + 1) ⟨true, Fin.castSucc (Fin.last j)⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  rw [blockIndex_true_last, e, ← hw'] at hent
  have a1 := unip_apply_castSucc_last k (j + 1) w' (Fin.last j)
  have a2 := unip_apply_castSucc_last k (m + j + 1) w (Fin.last (m + j))
  have : w'.toAdd (Fin.last j) = w.toAdd (Fin.last (m + j)) := by
    rw [← a1, ← a2]
    refine hent.trans ?_
    exact congrArg (fun g : GL (Fin (m + j + 1 + 1)) k => (g : Matrix (Fin (m + j + 1 + 1)) (Fin (m + j + 1 + 1)) k)
      (Fin.castSucc (Fin.last (m + j))) (Fin.last (m + j + 1))) hw.symm
  rw [this]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_unipotent_character_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (m j : ℕ) (u : MirUin k (m + (j + 1)))
    (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
    (gpProj k m (j + 1) ⟨u, hh⟩).1 = 1 ∧ ∃ hv : (gpProj k m (j + 1) ⟨u, hh⟩).2 ∈ MirUin k (j + 1),
      mirChar k ψ j ⟨_, hv⟩ = mirChar k ψ (m + j) u := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.gpProj_mirUin_char
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem exists_mirUin_gpProj_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  intro k _ _ _ _ m j n
  obtain ⟨v, hv, e⟩ := GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip k m (j + 1) (n : Mir k (j + 1)) n.2
  exact ⟨⟨v, hv⟩, v.2, e⟩

end GlobalTheory.CompanionTheory.LeibPhi

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_lift_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi

open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in

theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff, mem_mirabolicParabolic_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parabolic_iff_mem_embedded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)), y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaProj

theorem blockIndex_succ_false (m j : ℕ) (a : Fin m) :
    eGP m (j + 1) ⟨false, a⟩ = (Fin.castSucc (eGP m j ⟨false, a⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_succ_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = (Fin.castSucc (eGP m j ⟨true, b⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
    | (simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]; omega)

theorem blockIndex_succ_true_last (m j : ℕ) :
    eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = (Fin.last (m + j + 1) : Fin (m + j + 1 + 1)) := by
  exact GlobalTheory.BZMir.Leib.blockIndex_true_last m (j + 1)

theorem glEmbMat_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem gpProj_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1)),
    gpProj k m (j + 1) ⟨_, hh⟩ = ((gpProj k m j y).1, embedding₂ k j (gpProj k m j y).2) := by
  intro k _ _ _ _ m j y hh
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) false a b).trans
      (Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
        (GlobalTheory.BZMir.Leib.hgpIncl k m j y) false a b).symm)
    rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j a, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j b]
    exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
      ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _
  · apply Subtype.ext
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) true a b).trans ?_
    have hR := fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j y) true a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k)).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) b).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) a).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _).trans
          ((hR a b).symm.trans
            (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (j + 1)
              ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
                Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b).symm)

end GlobalTheory.CompanionTheory.LeibPhi.IotaProj

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_proj_embedding_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1)),
    gpProj k m (j + 1) ⟨_, hh⟩ = ((gpProj k m j y).1, embedding₂ k j (gpProj k m j y).2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.IotaProj.gpProj_iotaM
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_double_coset_dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | exact GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy <;> assumption)
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_gpProj_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) :=
  GlobalTheory.CompanionTheory.BZMir.continuous_gpProj

end GlobalTheory.CompanionTheory.LeibPhi
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.continuous_gpProj_phi
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_mirabolic_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM <;> assumption)
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (u : GL (Fin (n + 1)) k)).mp u.2
  have hrow' : ∀ j, ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      (Pi.single (Fin.last n) (1 : k) : Fin (n + 1) → k) j := by
    intro j
    rw [hrow]
    rfl
  have hblk : ∀ i j : Fin n,
      ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    exact congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hu
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n)), ?_⟩
  apply Units.ext
  ext i j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n))))) i j = _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, hrow']
    | cast j =>
      simp [GlobalTheory.BZMir.colMat, hrow', Matrix.one_apply, Pi.single_apply, Fin.castSucc_ne_last,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last, hblk]

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_twist_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.TwCInd.nonempty_twist_cInd_equiv
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩


theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactInduction_congr_equiv : ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CIndCongr.nonempty_equiv_cInd
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_functor_twist_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (j : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (j + 1)) W) (t : ℝ),
    Nonempty ((phiMinus k ψ (twist τ (dpowM (j + 1) t))).Equiv (twist (phiMinus k ψ τ) (dpowM j t))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | exact GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv | (intros; apply GlobalTheory.CompanionTheory.LeibPhiTw.phiMinus_twist_equiv <;> assumption)
end

section
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_parabolic_proj_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LeibPhi.dpowM_hgp
end

section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section AbsMain
variable {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem coinv_cInd (H U : Subgroup G) (hUH : U ≤ H) (hUn : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hι : Continuous ι) (hstab : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (H' : Subgroup G') (hH' : ∀ x, x ∈ H' ↔ ι x ∈ H)
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ H' W') (q : W →ₗ[ℂ] W')
    (hqs : Function.Surjective q)
    (hq : ∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w))
    (hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hD : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hcl : IsClosed {g : G | ∃ h ∈ H, ∃ x : G', g = h * ι x})
    (hemb : ∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ')
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hcomp : ∃ K' ∈ 𝓝 (1 : G'), IsCompact K') :
    Nonempty ((twAct (cInd H σ) U θ ι hstab).Equiv (cInd H' σ')) := by
  classical
  have hex := GlobalTheory.T.quotient_map_intertwines_restriction H H' ι σ σ' q hι hH' hq hcl hemb hcomp
  choose T hT using hex
  have hext : ∀ F F' : cIndSpace H' σ', (∀ x, F.1.1.1 x = F'.1.1.1 x) → F = F' := fun F F' h =>
    Subtype.ext (Subtype.ext (Subtype.ext (funext h)))
  let Tl : cIndSpace H σ →ₗ[ℂ] cIndSpace H' σ' :=
    { toFun := T
      map_add' := fun a b => hext _ _ fun x => by
        rw [hT]
        show _ = (T a).1.1.1 x + (T b).1.1.1 x
        rw [hT, hT, ← map_add]
        rfl
      map_smul' := fun c a => hext _ _ fun x => by
        rw [hT]
        show _ = c • (T a).1.1.1 x
        rw [hT, ← map_smul]
        rfl }
  have hTl : ∀ f x, (Tl f).1.1.1 x = q (f.1.1.1 (ι x)) := hT
  have hkill : twKer (cInd H σ) U θ ≤ LinearMap.ker Tl := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, e, rfl⟩
    show Tl _ = 0
    refine hext _ _ fun x => ?_
    rw [hTl]
    obtain ⟨hv, hθ⟩ := hstab x u
    have hvH : ι x * (u : G) * (ι x)⁻¹ ∈ H := hUH hv
    have e1 : (cInd H σ (u : G) e - (θ u : ℂ) • e).1.1.1 (ι x) =
        σ ⟨_, hvH⟩ (e.1.1.1 (ι x)) - (θ ⟨_, hv⟩ : ℂ) • e.1.1.1 (ι x) := by
      rw [hθ]
      show e.1.1.1 (ι x * (u : G)) - (θ u : ℂ) • e.1.1.1 (ι x) = _
      have e2 := e.1.1.2 ⟨_, hvH⟩ (ι x)
      have e3 : e.1.1.1 (ι x * (u : G)) = e.1.1.1 (ι x * (u : G) * (ι x)⁻¹ * ι x) := by
        congr 1; group
      rw [e3]
      exact congrArg (· - _) e2
    rw [e1]
    show _ = (0 : W')
    exact (hker _).2 (Submodule.subset_span ⟨⟨_, hv⟩, _, rfl⟩)
  let Tq := (twKer (cInd H σ) U θ).liftQ Tl hkill
  have hinj : Function.Injective Tq := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : Tl f = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).2 (GlobalTheory.T.jacquet_kernel_span_twisted_character H U hUH hUn θ ι hstab σ q hσ hker hD hbase f fun x => ?_)
    rw [← hTl, h0]
    rfl
  have hsurj : Function.Surjective Tq := by
    intro F
    obtain ⟨f, hf⟩ := GlobalTheory.T.quotient_map_induced_surjective_intertwiner H H' ι σ σ' q hι hσ hqs hH' hq hemb hbase F
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    show Tl f = F
    exact hext _ _ fun x => by rw [hTl, hf]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Tq ⟨hinj, hsurj⟩) fun y => ?_⟩
  refine LinearMap.ext fun z => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine hext _ _ fun x => ?_
  have e1 : (twAct (cInd H σ) U θ ι hstab y) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (cInd H σ (ι y) f) := rfl
  show (Tq (twAct (cInd H σ) U θ ι hstab y (Submodule.Quotient.mk f))).1.1.1 x =
    (Tq (Submodule.Quotient.mk f)).1.1.1 (x * y)
  rw [e1]
  show (Tl _).1.1.1 x = (Tl f).1.1.1 (x * y)
  rw [hTl, hTl, map_mul]
  rfl

end AbsMain

section PhiProd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem phiMinus_prodGP (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ}
    (a : Representation ℂ (GL (Fin m) k) V) (b : Representation ℂ (Mir k (j + 1)) W)
    (ha : IsSmooth a) (hb : IsSmooth b) :
    Nonempty ((phiMinus k ψ (n := m + j) (prodGP a b)).Equiv (prodGP a (phiMinus k ψ b))) := by
  classical
  have hsm : IsSmooth ((extTensor a b).comp (gpProj k m (j + 1))) := by
    intro w
    exact (isSmooth_extTensor ha hb w).preimage (GlobalTheory.T.continuous_parabolic_proj k m (j + 1))
  have hUH : MirUin k (m + (j + 1)) ≤ MirabolicParabolic k m (j + 1) := GlobalTheory.T.mirabolic_unipotent_le_parabolic k m (j + 1)
  let q : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] (TwJacquet b (MirUin k (j + 1)) (mirChar k ψ j)) :=
    LinearMap.lTensor V (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
  have hqs : Function.Surjective q := LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have hq : ∀ (h : MirabolicParabolic k m j) (hh : embedding₂ k (m + j) h ∈ MirabolicParabolic k m (j + 1)) (w : V ⊗[ℂ] W),
      q (((extTensor a b).comp (gpProj k m (j + 1))) ⟨embedding₂ k (m + j) h, hh⟩ w) =
        ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) h (q w) := by
    intro h hh w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v w =>
      have e := GlobalTheory.T.parabolic_proj_embedding_compat k m j h hh
      show q (extTensor a b (gpProj k m (j + 1) ⟨_, hh⟩) (v ⊗ₜ w)) =
        extTensor a (phiMinus k ψ b) (gpProj k m j h) (q (v ⊗ₜ w))
      rw [e]
      simp only [q, LinearMap.lTensor_tmul, extTensor_tmul]
      rfl
  have hker : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : MirUin k (m + (j + 1))) (v : V ⊗[ℂ] W),
      y = ((extTensor a b).comp (gpProj k m (j + 1))) ⟨u, hUH u.2⟩ v - (mirChar k ψ (m + j) u : ℂ) • v} := by
    intro w
    constructor
    · intro hw
      have hex := lTensor_exact V (LinearMap.exact_subtype_mkQ
        (twKer b (MirUin k (j + 1)) (mirChar k ψ j))) (Submodule.mkQ_surjective _)
      obtain ⟨t, rfl⟩ := (hex w).1 hw
      clear hw
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
      | tmul v x =>
        obtain ⟨x, hx⟩ := x
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        induction hx using Submodule.span_induction with
        | zero => simp
        | add x y _ _ hx hy =>
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
        | smul c x _ hx =>
          rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem _ c hx
        | mem x hx =>
          obtain ⟨n, w', rfl⟩ := hx
          obtain ⟨u, hh, e⟩ := GlobalTheory.T.exists_unipotent_lift_parabolic_proj k m j n
          obtain ⟨-, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u hh
          refine Submodule.subset_span ⟨u, v ⊗ₜ w', ?_⟩
          have e2 : (⟨_, hv⟩ : MirUin k (j + 1)) = n := Subtype.ext (congrArg Prod.snd e)
          rw [e2] at hθ
          show _ = extTensor a b (gpProj k m (j + 1) ⟨u, hh⟩) (v ⊗ₜ w') - _
          rw [e, hθ, extTensor_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          simp
    · intro hw
      induction hw using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
      | mem x hx =>
        obtain ⟨u, y, rfl⟩ := hx
        obtain ⟨e1, hv, hθ⟩ := GlobalTheory.T.parabolic_proj_unipotent_character_compat k ψ m j u (hUH u.2)
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          have := congrArg₂ (· + ·) hx hy
          simp only [add_zero, ← map_add] at this
          rw [← this]
          congr 1
          simp only [map_add, smul_add]
          abel
        | tmul v w =>
          show q (extTensor a b (gpProj k m (j + 1) ⟨u, hUH u.2⟩) (v ⊗ₜ w) - _) = 0
          rw [extTensor_tmul, e1, ← hθ, map_one, Module.End.one_apply, map_sub, map_smul]
          simp only [q, LinearMap.lTensor_tmul]
          rw [← TensorProduct.tmul_smul, ← TensorProduct.tmul_sub, ← map_smul, ← map_sub]
          have : (twKer b (MirUin k (j + 1)) (mirChar k ψ j)).mkQ
              (b (gpProj k m (j + 1) ⟨u, hUH u.2⟩).2 w - (mirChar k ψ j ⟨_, hv⟩ : ℂ) • w) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨⟨_, hv⟩, w, rfl⟩
          rw [this, TensorProduct.tmul_zero]
  refine coinv_cInd (MirabolicParabolic k m (j + 1)) (MirUin k (m + (j + 1))) hUH (GlobalTheory.T.mirabolic_unipotent_normal k _) (mirChar k ψ (m + j))
    (embedding₂ k (m + j)) (GlobalTheory.T.continuous_mirabolic_embedding k _) (levi_stab ψ (m + j)) (MirabolicParabolic k m j) (GlobalTheory.T.mem_parabolic_iff_mem_embedded k m j)
    ((extTensor a b).comp (gpProj k m (j + 1))) hsm ((extTensor a (phiMinus k ψ b)).comp (gpProj k m j)) q
    hqs hq hker ?_ (GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic k m j) (GlobalTheory.T.embedded_small_neighbourhood_factor k m j) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k _) ?_
  · intro g
    rcases GlobalTheory.T.mirabolic_double_coset_dichotomy k ψ hψ1 m j g with h | ⟨u, hx, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨u, hx, fun w => ?_, h2⟩
      simp [h1]
  · obtain ⟨K, hKo, hKc, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j) Set.univ Filter.univ_mem
    exact ⟨K, hKo.mem_nhds (one_mem K), hKc⟩

end PhiProd

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist ρ' χ) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => by
    refine LinearMap.ext fun v => ?_
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    show e.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • ρ' g (e.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ h

def extEquiv {G₁ G₂ M V V' W W' : Type} [Group G₁] [Group G₂] [Group M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ G₁ V} {a' : Representation ℂ G₁ V'} {b : Representation ℂ G₂ W}
    {b' : Representation ℂ G₂ W'} (e : a.Equiv a') (f : b.Equiv b') (s : M →* G₁ × G₂) :
    Representation.Equiv ((extTensor a b).comp s) ((extTensor a' b').comp s) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) fun g => by
    refine TensorProduct.ext' fun v w => ?_
    have h1 := LinearMap.congr_fun (e.isIntertwining' (s g).1) v
    have h2 := LinearMap.congr_fun (f.isIntertwining' (s g).2) w
    show TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (extTensor a b (s g) (v ⊗ₜ w)) =
      extTensor a' b' (s g) (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv (v ⊗ₜ w))
    rw [extTensor_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul, extTensor_tmul]
    exact congrArg₂ _ h1 h2

theorem isOpen_ker_dpowM (n : ℕ) (s : ℝ) :
    IsOpen (((dpowM (k := k) n s).ker : Subgroup (Mir k n)) : Set (Mir k n)) :=
  (isOpen_ker_dpow k (n + 1) s).preimage continuous_subtype_val

theorem prodGP_congr {m j : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {a : Representation ℂ (GL (Fin m) k) V} {a' : Representation ℂ (GL (Fin m) k) V'}
    {c : Representation ℂ (Mir k j) W} {c' : Representation ℂ (Mir k j) W'} (e : a.Equiv a') (f : c.Equiv c') :
    Nonempty ((prodGP a c).Equiv (prodGP a' c')) :=
  GlobalTheory.T.compactInduction_congr_equiv (MirabolicParabolic k m j) _ _ (extEquiv e f (gpProj k m j))

theorem tw_rep {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    twist ((extTensor a c).comp (gpProj k m j)) ((dpowM (m + j) r).comp (MirabolicParabolic k m j).subtype) =
      (extTensor (twist a (dpow m r)) (twist c (dpowM j r))).comp (gpProj k m j) := by
  refine MonoidHom.ext fun h => LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v w =>
    show (dpowM (m + j) r (h : Mir k (m + j)) : ℂ) • extTensor a c (gpProj k m j h) (v ⊗ₜ w) =
      extTensor (twist a (dpow m r)) (twist c (dpowM j r)) (gpProj k m j h) (v ⊗ₜ w)
    rw [extTensor_tmul, extTensor_tmul, twist_apply, twist_apply, GlobalTheory.T.modulus_parabolic_proj_factor k m j r h, Units.val_mul,
      TensorProduct.smul_tmul_smul]

theorem cInd_of_eq {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) {σ σ' : Representation ℂ H W} (h : σ = σ') : Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  subst h; exact ⟨Representation.Equiv.refl _⟩

theorem twist_prodGP {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (a : Representation ℂ (GL (Fin m) k) V) (c : Representation ℂ (Mir k j) W) (r : ℝ) :
    Nonempty ((twist (prodGP a c) (dpowM (m + j) r)).Equiv (prodGP (twist a (dpow m r)) (twist c (dpowM j r)))) := by
  have A2 := GlobalTheory.T.compactInduction_twist_equiv (MirabolicParabolic k m j) ((extTensor a c).comp (gpProj k m j)) (dpowM (m + j) r) (isOpen_ker_dpowM _ _)
  have B := cInd_of_eq (MirabolicParabolic k m j) (tw_rep a c r)
  obtain ⟨A2⟩ := A2
  obtain ⟨B⟩ := B
  have C := A2.trans B
  unfold prodGP
  exact ⟨C⟩

def eqvOfEq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ ρ' : Representation ℂ G V} (h : ρ = ρ') :
    ρ.Equiv ρ' := h ▸ Representation.Equiv.refl ρ

theorem main_twisted (ψ : AddChar k Circle) (hψ1 : ψ ≠ 1) {m j : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin m) k) V)
    (τ : Representation ℂ (Mir k (j + 1)) W) (hρ : IsSmooth ρ) (hτ : IsSmooth τ) (s₀ s₁ t r : ℝ) (hs : r + s₀ = s₁) :
    Nonempty ((twist (phiMinus k ψ (n := m + j) (prodGP (twist ρ (dpow m s₀)) (twist τ (dpowM (j + 1) t))))
      (dpowM (m + j) r)).Equiv
      (prodGP (twist ρ (dpow m s₁)) (twist (twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t)))) := by
  have ha : IsSmooth (twist ρ (dpow (k := k) m s₀)) := isSmooth_twist hρ (isOpen_ker_dpow k m s₀)
  have hb : IsSmooth (twist τ (dpowM (k := k) (j + 1) t)) := isSmooth_twist hτ (isOpen_ker_dpowM _ _)
  have E0 := phiMinus_prodGP ψ hψ1 (twist ρ (dpow (k := k) m s₀)) (twist τ (dpowM (k := k) (j + 1) t)) ha hb
  have A2 := twist_prodGP (twist ρ (dpow (k := k) m s₀)) (phiMinus k ψ (twist τ (dpowM (k := k) (j + 1) t))) r
  obtain ⟨E0⟩ := E0
  obtain ⟨A2⟩ := A2
  have A4 : twist (twist ρ (dpow (k := k) m s₀)) (dpow m r) = twist ρ (dpow m s₁) := by
    rw [twist_twist, ← dpow_add, hs]
  have E3 := GlobalTheory.T.derivative_functor_twist_equiv k ψ j W τ t
  obtain ⟨E3⟩ := E3
  have A5 : (twist (twist (phiMinus k ψ τ) (dpowM j t)) (dpowM j r)) =
      twist (twist (phiMinus k ψ τ) (dpowM j r)) (dpowM j t) := by
    rw [twist_twist, twist_twist, mul_comm]
  have E5 := (twistEquiv E3 (dpowM j r)).trans (eqvOfEq A5)
  have E7 := prodGP_congr (eqvOfEq A4) E5
  obtain ⟨E7⟩ := E7
  exact ⟨(twistEquiv E0 _).trans (A2.trans E7)⟩

end Final

theorem phiGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  intro k _ _ _ _ ψ _ hψ1 m j ρ τ hρ hτ
  have X := main_twisted ψ hψ1 ρ.ρ τ.ρ hρ hτ (((j + 1 + 1 : ℕ) : ℝ) / 2) (((j + 1 : ℕ) : ℝ) / 2) (-((m : ℕ) : ℝ) / 2)
    (-1 / 2) (by push_cast; ring)
  unfold MIso
  have e : ∀ h : m + (j + 1) = m + j + 1, mcast h (prodGPn ρ τ) = prodGPn ρ τ := fun _ => rfl
  rw [e]
  unfold phiN prodGPn mtw MRep.phiM GRep.tw
  exact X

end GlobalTheory.CompanionTheory.LeibPhi

end
end
