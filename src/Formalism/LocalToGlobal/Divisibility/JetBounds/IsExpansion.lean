module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
public import Formalism.GaussJetBounds.OneLetterGauss
public import Formalism.GaussJetBounds.GenLogInverse
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

attribute [instance] PathData.fPi

section Paths

variable {K : Type} [Field K] {l : ℕ} [Fact l.Prime] {J A B : Type} [Fintype J] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

end Paths

section PathsW

variable {K : Type} [Field K] [NumberField K] [StarRing K] {l : ℕ} [Fact l.Prime] {J A B : Type} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

end PathsW

end Formalism.L2.DIV
