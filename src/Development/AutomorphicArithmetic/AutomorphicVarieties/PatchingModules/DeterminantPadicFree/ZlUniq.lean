module

public import Mathlib.NumberTheory.Padics.RingHoms
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem zlUniq_val (l : ℕ) [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hl : (l : R) = 0) (a : ℤ_[l]) : f a = ((PadicInt.toZMod a).val : R) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (PadicInt.maximalIdeal_eq_span_p (p := l) ▸ PadicInt.sub_zmodRepr_mem a)
  rw [PadicInt.val_toZMod_eq_zmodRepr]
  have h := congrArg f hc
  rw [map_mul, map_natCast, hl, mul_zero, map_sub, map_natCast, eq_comm, sub_eq_zero] at h
  exact h

theorem UpperTheory.V.Pa.Det.zlUniq :
    ∀ (l : ℕ) [Fact l.Prime], (∀ {K : Type} [Field K] [Finite K] (_ : ℤ_[l] →+* K), CharP K l) ∧ ∀ {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R), (l : R) = 0 → f = f' ∧ ∀ a, f a = ((PadicInt.toZMod a).val : R) := by
  intro l _
  refine ⟨fun {K} _ _ f => ?_, fun {R} _ f f' hl => ⟨?_, zlUniq_val l f hl⟩⟩
  · obtain ⟨p, hchar⟩ := CharP.exists K
    have hp : p.Prime := CharP.char_is_prime K p
    have hpl : p = l := by
      by_contra hne
      have hunit : IsUnit (p : ℤ_[l]) := by
        by_contra hnu
        have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
          rw [Int.cast_natCast]
          exact PadicInt.mem_nonunits.mp hnu
        rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
        exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
      have h := hunit.map f
      rw [map_natCast, CharP.cast_eq_zero] at h
      exact not_isUnit_zero h
    subst hpl
    exact hchar
  · ext a
    rw [zlUniq_val l f hl, zlUniq_val l f' hl]
