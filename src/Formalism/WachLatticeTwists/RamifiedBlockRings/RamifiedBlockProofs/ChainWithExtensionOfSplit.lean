import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CompositeOfChainHolds

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem chain_from_primitive_data : ChainFromPrimitiveData := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨hP, hA, h2, hG3, hε⟩ := hyp
  obtain ⟨eB, e₁, hI⟩ := idem O X T d G r π t bl χ₁ ε hP hA h2
  obtain ⟨m, jj, a, hja, hsep⟩ := x0 O X T d G r π t bl χ₁ ε hP eB e₁ hI hG3 g₀ hε L ϖ hϖ
  refine ⟨eB, e₁, fun x => ϖ ^ L • ∑ i, jj i x • (eB x * a i x * eB x),
    ⟨hI, ⟨m, jj, a, hja, rfl⟩, hsep⟩, ?_⟩
  intro O' _ _ _ _ _ _ e he hspl
  obtain ⟨b1, b2, b3, b4⟩ := bridge O X T d G r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  obtain ⟨cP, cA, cI, cX, cv⟩ := stageC O O' e he X T d G r π t bl χ₁ ε hP hA eB e₁ hI g₀ _ b1 b2 b3 b4
    hsep hspl
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5⟩, i3', hT⟩ := ring_objects_exist O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _
    cP cA _ _ cI g₀ _ cX
  have hpπ : D.p D.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  refine ⟨D, hD, ⟨i1, i2, i3', i4, i5, hT, fun Z => ?_⟩, fun Z => by rw [hpπ]; exact cv Z⟩
  exact displayFree O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _ cP cA _ _ cI g₀ _ cX D hD hT Z



end Formalism.RepresentationBoundsCohomology.ringDataObjects
