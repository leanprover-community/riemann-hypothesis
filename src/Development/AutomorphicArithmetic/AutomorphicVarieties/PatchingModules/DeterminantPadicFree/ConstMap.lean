module

public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.constMap :
    ∀ {K K' : Type} [Field K] [Finite K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), ∃ ι : K →+* K', ∀ a, j (PowerSeries.C a) = PowerSeries.C (ι a) := by
  intro K K' _ _ _ j
  classical
  haveI := Fintype.ofFinite K
  set p := ringChar K with hpdef
  haveI : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  set e : K →+* PowerSeries K' := j.comp PowerSeries.C
  haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p
  have key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    set c := PowerSeries.constantCoeff f with hcdef
    have hc : c ^ (p ^ (n : ℕ)) = c := by
      have h2 := congrArg PowerSeries.constantCoeff hf
      rw [map_pow] at h2
      exact h2
    have hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c := by
      rw [sub_pow_char_pow, hf, ← map_pow, hc]
    have hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]
    have hq1 : 1 ≤ p ^ (n : ℕ) - 1 := by
      have h1 : 2 ≤ p := hp.two_le
      have h3 : p ≤ p ^ (n : ℕ) := Nat.le_self_pow (PNat.ne_zero n) p
      omega
    have hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h4 := congrArg PowerSeries.constantCoeff h
      rw [map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero] at h4
      exact zero_ne_one (sub_eq_zero.mp h4)
  refine ⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩
  have ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a) := by
    rw [← map_pow, ← map_pow, ← hq, FiniteField.pow_card]
  exact key _ ha
