import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLatticeExchange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCOPrXCgrp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralTranslateIndicator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LatPair.VolStep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_lat {n : Type} [Fintype n] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact (L : Set (n → k)) := by
  classical
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h0 : IsCompact (stdLat k n : Set (n → k)) := by
    have := isCompact_univ_pi fun _ : n => isCompact_int k
    convert this using 1
    ext x
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have h1 := h0.image (f := fun x : n → k => g.val *ᵥ x) (continuous_const.matrix_mulVec continuous_id)
  convert h1 using 1
  ext x
  simp only [SetLike.mem_coe, mem_smul_iff, Set.mem_image]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show g • (g⁻¹ • x) = x
    simp
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ • (g • y) ∈ _
    simpa using hy

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_flagIn {n : Type} (c i : ℕ) : Continuous (flagIn (k := k) (n := n) c i) := by
  refine continuous_pi fun j => ?_
  rcases j with r | l
  · exact continuous_apply _
  · by_cases h : l.val < i
    · simp only [flagIn, Sum.elim_inr, dif_pos h]
      exact continuous_apply _
    · simp only [flagIn, Sum.elim_inr, dif_neg h]
      exact continuous_const

theorem region_eq {n : Type} (c : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) :
    {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} =
      (fun y : n ⊕ Fin i → k => q.inv • flagIn c i y) ⁻¹' (L : Set (n ⊕ Fin c → k)) := by
  ext y
  refine ⟨fun h => h.1, fun h => ⟨h, fun l hl => ?_⟩⟩
  simp [flagIn, not_lt.2 hl]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (q : Unif k) (ν : Measure k) [ν.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k] (i : ℕ), i ≤ c → IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} ∧ volStep ν q L i ≠ 0 ∧ volStep ν q L i ≠ ⊤ := by
  intro k _ _ _ _ _ _ n _ _ c q ν _ L _ i hi
  haveI := secondCountable k
  haveI := t2Space k
  have ho : IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} := by
    rw [region_eq]
    exact (isClopen_lattice L).2.preimage ((continuous_flagIn c i).const_smul q.inv)
  refine ⟨ho, ?_, ?_⟩
  · refine ho.measure_ne_zero _ ⟨0, ?_⟩
    rw [region_eq]
    have : flagIn (k := k) (n := n) c i 0 = 0 := by
      funext j
      rcases j with r | l <;> simp [flagIn]
    simp [this]
  · have hK := (isCompact_lat L).image
      (f := fun (z : n ⊕ Fin c → k) (j : n ⊕ Fin i) => ((q.1 : 𝒪[k]) : k) * z (Sum.map id (Fin.castLE hi) j)) (by fun_prop)
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := Measure.pi fun _ : n ⊕ Fin i => ν)).ne (measure_mono ?_)
    rw [region_eq]
    intro y hy
    refine ⟨_, hy, ?_⟩
    funext j
    rcases j with r | l
    · simp [flagIn, Unif.inv, q.ne_zero]
    · simp [flagIn, Unif.inv, q.ne_zero]

end GlobalTheory.LatPair.VolStep
end
end

section
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} {q : Unif k}

theorem oneOrbit : OneOrbit k n c q := by
  have h1 : ∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
      ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂ := by
    intro L₁ L₂ f₁ f₂ g₁ g₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n k) (glue g₁) (glue g₂)
    refine ⟨g, by rw [← glue_ker g₁, ← Pair.smul_ker, hg, glue_ker], ?_⟩
    have := (glue_hasVal g₁).gl_smul g
    rwa [hg, Pair.hasVal_one_iff (glue_hasVal g₂), glue_ker] at this
  refine ⟨h1, fun L₀ _ Q h₀ e h => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, L'', f'', hG, H⟩
    obtain ⟨g, hg, hg'⟩ := h1 _ _ _ _ (Pair.isGlue Q.hasVal_vec) hG
    refine ⟨u * embX c g, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩),
      (u * embX c g * h₀)⁻¹ * h, ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, mul_smul, mul_smul, e, embX_smul_gluedS, hg, H,
      gluedS_congr hg']
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    obtain ⟨g, u, hu, rfl⟩ := Radical.exists_of_mem_R hr
    refine ⟨_, Radical.conj_mem g hu, g • Q.ker, g • Q.vec, ?_, ?_⟩
    · simpa using Pair.isGlue (Q.hasVal_vec.gl_smul g)
    · rw [← embX_smul_gluedS, ← e, mul_smul _ κ, show κ • L₀ = L₀ from hκ]
      simp only [mul_smul, inv_smul_smul]

instance isLattice_interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [hL : L.IsLattice k] : (interX L).IsLattice k := by
  refine ⟨Submodule.fg_of_fg_map_injective (inX k n c) (fun x y h => funext fun r => congrFun h (Sum.inl r))
    (hL.fg.of_le (Submodule.map_comap_le _ _)), ChainLattice.span_eq_top_of_smul_mem _ fun v => ?_⟩
  obtain ⟨a, ha, hav⟩ := ChainLattice.exists_smul_mem (K := k) L (v := inX k n c v) (by rw [hL.span_eq_top]; trivial)
  exact ⟨a, ha, by rw [interX, Submodule.mem_comap, map_smul]; exact hav⟩

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]

end GlobalTheory.LevelUnfold
end
end
