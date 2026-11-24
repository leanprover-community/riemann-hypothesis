module

public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.WittVector.Identities

@[expose] public section

namespace GlobalTheory

theorem charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h3 : p ∣ l := (CharP.cast_eq_zero_iff K p l).1 h2
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h3
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

end GlobalTheory
