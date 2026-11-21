import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.OneCosetSymmetricAndNonvanishing
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
import Formalism.LocalToGlobal.Columns.FrameEntryAuxiliarySuperdiagonal
import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Closed

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)


end Closed

end Formalism.L2.Col
