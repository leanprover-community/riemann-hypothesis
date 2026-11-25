module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC
import Development.EtaleCohomology.EtaleSheaves.DomOpenPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Polynomial

namespace GlobalTheory.FractionRingRootRange

theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intros
  apply _root_.GlobalTheory.AICIff.root_mem_range <;> assumption

theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  apply LateralTheory.E.DomOpenPf.algClosed_of_AIC <;> assumption

end GlobalTheory.FractionRingRootRange
