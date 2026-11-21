import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLb
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowest_K_type_integral_formula (D : D7) (h : PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) : StandardLattice.SmallPrimeLengthBound D := h



def IdxColTie (D : D7) : Prop := StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) = S.gaG D

def IdxRowTie (D : D7) : Prop := StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) = LocalBesselAndTopKernel.idxRows D

def ColHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧ ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u





end Formalism.MainNotions.J

end
