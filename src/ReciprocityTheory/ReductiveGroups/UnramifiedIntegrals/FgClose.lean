module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem cm3 : CM3 :=
  GlobalTheory.HondaCM3.cm3

end ReciprocityTheory.ChartRestriction.L1
