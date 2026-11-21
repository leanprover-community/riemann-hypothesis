import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLj
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}





theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

theorem gains_losses_eq_defined (Gi : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (X : ErrX D) (c : ErrC)
    (hF : ∀ w, Formalism.MainNotions.G.ParametersFill Gi K w) (hE : L.EDef X K c) : Formalism.MainNotions.LocalQuadraticParts.ZeroGainAbove L := stmtZ Gi K X c hF hE

end Formalism.MainNotions.J

end
