module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.CharacterFactorUnitaryAction
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

end SeamU

end Formalism.L2.Ker
