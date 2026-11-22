module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basics
variable {m : ℕ}

end Basics

section Mask
variable {N : ℕ} (P : Fin N → Fin N → Prop) [DecidableRel P]

end Mask

section Rep
variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

end Rep

section Parab
variable {M : ℕ}

end Parab

section Main

end Main

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
