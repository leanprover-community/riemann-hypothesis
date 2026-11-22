module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.TwistVertex

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem val_embX (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := rfl

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  refine mem_KO.2 ⟨?_, ?_⟩
  · rw [val_embX]; exact intM_fromBlocks.2 ⟨h1, intM_zero, intM_zero, intM_one⟩
  · rw [← map_inv, val_embX]; exact intM_fromBlocks.2 ⟨h2, intM_zero, intM_zero, intM_one⟩

end General

section Empty
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}

end Empty

end GlobalTheory.TwistVertex
