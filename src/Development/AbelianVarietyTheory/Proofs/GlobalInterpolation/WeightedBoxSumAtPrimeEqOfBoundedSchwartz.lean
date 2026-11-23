module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowDvdOfMulNatCastEqOfNotMemPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPiFinsetFinSuccCons
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumValsQOfInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory

theorem boxSum_eq_of_funBdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  intro E _ _ K _ _ P hq ι _ _ f N hf A B hA hB
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  unfold boxSum
  refine weighted_sum_piFinset ι E K
    (fun g => (∀ a, g a ≠ 0 → IntAt P ((qOf P : E) ^ N * a)) ∧
      ∀ a u, IntAt P u → g (a + (qOf P : E) ^ N * u) = g a) _ _ _ _ ?_ f ?_
  · rintro g ⟨h1, h2⟩
    rw [sum_valsQ_of_invariant E P K g N h2 A B hB,
      sum_valsQ_eq_of_support_intAt E P hq K g N h1 A N hA]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  · intro t i
    refine ⟨fun a ha => ?_, fun a u hu => ?_⟩
    · simpa using hf.1 _ ha i
    · have e : Function.update t i (a + (qOf P : E) ^ N * u)
          = Function.update t i a + ((qOf P : E) ^ N) • (Pi.single i u : ι → E) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      simp only [e]
      refine hf.2 _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simpa [hj] using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

end GlobalTheory
