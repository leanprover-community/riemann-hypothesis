import Mathlib
import Development.AutomorphicArithmetic.TeichmullerLogarithm.CyclotomicPowSubOneNilpotent

open Ideal Reformulated.AutPerF

universe u

namespace UpperTheory.RingBr




variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R] [IsAlgClosed (FractionRing R)]


end UpperTheory.RingBr
