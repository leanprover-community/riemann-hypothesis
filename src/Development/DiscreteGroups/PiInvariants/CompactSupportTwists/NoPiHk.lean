module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Defs

end DiscreteGroups.T1.G

end
