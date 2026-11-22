module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs

@[expose] public section

open KStar.TotallyRealRoots

namespace KStar.IdealValuations

variable (l : ℕ) [Fact l.Prime]

variable {l} in
noncomputable def complField {E : Type*} [Field E] (j : E →+* PadicAlgCl l) :
    IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range j)

end KStar.IdealValuations
