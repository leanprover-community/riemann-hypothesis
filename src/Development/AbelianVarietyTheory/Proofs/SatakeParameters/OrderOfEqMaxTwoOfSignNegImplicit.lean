import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
import BuildAid.ForwardExisting

section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  atlas_forward_decl GlobalTheory.orderOf_moving_stmt
