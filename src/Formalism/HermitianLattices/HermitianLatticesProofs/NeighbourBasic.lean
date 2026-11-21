import Mathlib
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Quot

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]





end Quot

section DedekindLFunctions

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


end DedekindLFunctions

section Main

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]




end Main

end Formalism.HermitianLatticesTheory
