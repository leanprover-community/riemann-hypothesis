module

public import Formalism.SizeWindowBrackets.SChain
public import Formalism.SizeWindowBrackets.ClaimGaFree
public import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
public import Formalism.SizeWindowBrackets.GaloisToProductIsIso
public import Formalism.SizeWindowBrackets.WindowSettingSatisfiable

@[expose] public section

open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

section Places
variable {K : Type} [Field K] [NumberField K]

end Places

attribute [instance] Fam.indexKFirst Fam.indexKSecond Fam.indexKThird Fam.indexKFourth Fam.indexWFirst Fam.indexWSecond Fam.indexWThird Fam.indexWFourth Fam.firstRealIndex Fam.secondRealIndex Fam.firstRationalIndex Fam.secondRationalIndex
  Fam.indexVFirst Fam.indexVSecond Fam.indexVThird Fam.indexVFourth Fam.indexCFirst Fam.indexCSecond Fam.indexFFirst Fam.indexFSecond Fam.indexFThird Fam.indexFFourth Fam.indexDFirst Fam.indexDSecond

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

end Fam

section Data
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

variable [∀ u0, Nonempty (W u0)]

end Data

section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}

variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]

end Loss

section DataD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataD

section DataL
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataL

section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataT

section LossC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}

end LossC

end Formalism.LFunctionChainParameters.LChain2
