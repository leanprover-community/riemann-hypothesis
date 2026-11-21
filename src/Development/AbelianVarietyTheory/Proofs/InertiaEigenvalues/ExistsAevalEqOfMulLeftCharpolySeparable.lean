import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
import BuildAid.ForwardExisting

section
open Polynomial

namespace GlobalTheory.SepGenElt

theorem exists_aeval_eq : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  intro E A _ _ _ _ g hs x
  have hx : x ∈ Algebra.adjoin E ({g} : Set A) := by
    rw [GlobalTheory.SepGen.adjoin_eq_top g hs]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  exact hx

end GlobalTheory.SepGenElt
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  atlas_forward_decl GlobalTheory.SepGenElt.exists_aeval_eq
