import Mathlib
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.BaseInst

open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def gaussianPrimesSmall : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 5]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 2 1]
  Word := Unit
  T := fun _ => 14145788201
  piT := fun _ => gz ι LL hE 84101 84100

set_option maxRecDepth 1000000 in
theorem prime_fourteen_billion_example : Nat.Prime 14145788201 := by norm_num



end Gauss

end Formalism.L2.Col
