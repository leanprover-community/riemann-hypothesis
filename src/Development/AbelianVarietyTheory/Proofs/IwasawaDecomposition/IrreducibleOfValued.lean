module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open IsDedekindDomain NumberField
namespace GlobalTheory
namespace DegreeOneUniformiser

open IsDedekindDomain NumberField in
private theorem adicCompletionIntegers_integers {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers F) :=
  ⟨Subtype.val_injective, fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2,
    fun x hx => ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mpr hx⟩, rfl⟩⟩

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.DegreeOneUniformiser.irreducible_of_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletionIntegers F)
    (h : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) : Irreducible π := by
  have hI := adicCompletionIntegers_integers v
  have hunit : ∀ x : v.adicCompletionIntegers F, IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
    fun x => hI.isUnit_iff_valuation_eq_one
  have hle : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) ≤ 1 :=
    fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp x.2
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (hunit π).mp hu
    rw [h] at this
    exact absurd this (by decide)
  · have hv : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
        WithZero.exp (-1 : ℤ) := by
      rw [← h, hab, Subring.coe_mul, map_mul]
    have ha0 : Valued.v (a : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
    have hb0 : Valued.v (b : v.adicCompletion F) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (a : v.adicCompletion F) = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ha0).symm⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (b : v.adicCompletion F) = WithZero.exp n :=
      ⟨_, (WithZero.exp_log hb0).symm⟩
    have ha := hle a
    have hb := hle b
    rw [hm, hn, ← WithZero.exp_add, WithZero.exp_inj] at hv
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at ha
    rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    rw [hunit, hunit, hm, hn, ← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

end DegreeOneUniformiser
end GlobalTheory
