module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibre
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.TopOfMap
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

section
open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) :=
  _root_.GlobalTheory.dixmier_aeval_injective T hT p hp

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 :=
  _root_.GlobalTheory.dixmier_commutant_scalar ι V ρ hrank hirr T hT

end

theorem rank_SB (V : Type) [TopologicalSpace V] [SecondCountableTopology V] [T2Space V] :
    Module.rank ℂ (GlobalTheory.WeilM.SB V) ≤ Cardinal.aleph0 := by
  classical
  have hc : {K : Set V | IsCompact K ∧ IsOpen K}.Countable := by
    refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis V)).image Set.sUnion).mono ?_
    rintro K ⟨h1, h2⟩
    obtain ⟨S, hS, rfl⟩ := (TopologicalSpace.isBasis_countableBasis V).open_eq_sUnion h2
    obtain ⟨T, hT, hf, hcov⟩ := h1.elim_finite_subcover_image (b := S) (c := id)
      (fun s hs => (TopologicalSpace.isBasis_countableBasis V).isOpen (hS hs)) (by rw [Set.sUnion_eq_biUnion]; rfl)
    refine ⟨T, ⟨hf, hT.trans hS⟩, subset_antisymm (Set.sUnion_mono hT) ?_⟩
    rw [Set.sUnion_eq_biUnion (s := T)]; exact hcov
  have hle : GlobalTheory.WeilM.SB V ≤ Submodule.span ℂ ((fun K : Set V => K.indicator (1 : V → ℂ)) '' {K | IsCompact K ∧ IsOpen K}) := by
    intro f hf
    have hfin : (f '' tsupport f).Finite := by
      haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2.isCompact
      have h2 := (hf.1.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite
      rwa [Set.range_comp, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h2
    have e : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : V → ℂ) := by
      funext y
      rw [Finset.sum_apply, Finset.sum_eq_single (f y)]
      · simp
      · intro c _ hc
        simp [hc.symm]
      · intro h
        have : f y = 0 := by
          by_contra h0
          exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨y, subset_tsupport _ h0, rfl⟩⟩)
        simp [this]
    rw [e]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, hf.1 _⟩, rfl⟩)
    refine hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber c).1 fun y hy => subset_tsupport _ ?_
    rw [Function.mem_support, show f y = c from hy]
    exact (Finset.mem_erase.1 hc).1
  exact (Submodule.rank_mono hle).trans ((rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.2 (hc.image _).to_subtype))

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
