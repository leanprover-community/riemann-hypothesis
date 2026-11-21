import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateDeterminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve

universe u

section Tate

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
  [W.IsElliptic]


end Tate

section Galois

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsAlgClosed L]
  (W₀ : WeierstrassCurve K) [W₀.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]

end Galois

end GroundTheory.Arith.Abelian
