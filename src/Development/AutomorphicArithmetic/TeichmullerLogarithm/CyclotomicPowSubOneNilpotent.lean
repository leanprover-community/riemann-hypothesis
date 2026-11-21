import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta

open Ideal Reformulated.AutPerF

universe u

namespace UpperTheory.RingBr




variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]



end UpperTheory.RingBr
