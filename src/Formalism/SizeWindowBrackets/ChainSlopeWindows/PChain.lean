module

public import Formalism.SizeWindowBrackets.SChain
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LipschitzWeightAndMinimum
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe

@[expose] public section

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr

theorem size_windows_split : SizeWindowsSplit := by
  intro C ε x n nT nT2 m b k aE Err
  unfold SizeWindows RestSize errorBracketSizeWindows
  tauto

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

end

namespace Model

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

end Model

end Formalism.LFunctionChainParameters.LChain

section Check
open Formalism.LFunctionChainParameters.LChain
end Check

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr

namespace ModelEv

open Model

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

end ModelEv

namespace ModelText

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

end ModelText

end Formalism.LFunctionChainParameters.LChain

section Check2
open Formalism.LFunctionChainParameters.LChain
end Check2
