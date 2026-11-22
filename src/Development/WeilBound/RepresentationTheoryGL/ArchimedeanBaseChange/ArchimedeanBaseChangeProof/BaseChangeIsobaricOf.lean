module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitS
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.LocalL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.InertR
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.SplitSph
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.UnramB

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

end PositivityTheory.Rg.BcB

end
