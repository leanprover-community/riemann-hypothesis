module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem blockWeight_cast_eq_unitDeg {K : Type} [DecidableEq K] (ι : K → Type) (b : K) (i : ι b) :
    (fun k => ((blockWeight ι ⟨b, i⟩ k : ℕ) : ℤ)) = unitDeg b := by
  funext k
  simp only [blockWeight, unitDeg, Pi.single_apply]
  split_ifs <;> rfl


open Classical in
theorem IntersectionRecursion.proof : IntersectionRecursion.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim b i hX bs
  have : q.IsPrime := hq.isPrime
  set x : MRing ι F := X ⟨b, i⟩ with hxdef
  set J : Ideal (MRing ι F) := q ⊔ Ideal.span {x} with hJdef
  have hx : IsMultiHomog x (blockWeight ι ⟨b, i⟩) := isWeightedHomogeneous_X F _ _

  have hlt : ringKrullDim (MRing ι F ⧸ q) < ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (omega : d + 1 + Fintype.card K < d + 2 + Fintype.card K)
  have hcut := CutByForm.full F K ι d q hq.isPrime hq.multiHomog hlt x (blockWeight ι ⟨b, i⟩) hx hX bs
  rw [blockWeight_cast_eq_unitDeg] at hcut
  rw [hcut, cycEval]

  have hle : q ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk q x ∈ nonZeroDivisors (MRing ι F ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hX (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ q) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  rw [hdim] at hsucc
  have hJlt : ringKrullDim (MRing ι F ⧸ J) < ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    have h := HilbDegBound.lt_of_add_one_le_natCast hsucc
    rwa [show d + 1 + Fintype.card K = d + Fintype.card K + 1 by omega] at h
  have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

  refine finsum_congr fun W => ?_
  unfold divCycle
  by_cases hW : W ∈ J.minimalPrimes ∧ IsRelevant W
  · rw [dite_eq_left hW]
    have hWp : W.IsPrime := hW.1.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJh hW.1
    have hWle : ringKrullDim (MRing ι F ⧸ W) ≤ ringKrullDim (MRing ι F ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW.1.1.2)
        (Ideal.Quotient.factor_surjective hW.1.1.2)
    by_cases hWd : ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dite_eq_left ⟨⟨hWp, hWh, hW.2⟩, hW.1.1.2, hWd⟩]
    · rw [dite_eq_right fun h => hWd h.2.2]
      have hWlt : ringKrullDim (MRing ι F ⧸ W) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
        exact lt_of_le_of_ne
          (HilbDegBound.le_natCast_of_lt_natCast_succ (lt_of_le_of_lt hWle hJlt)) hWd
      rw [IntNumVanish.full F K ι d W hWp hWh (Or.inr hWlt) bs, mul_zero]
  · rw [dite_eq_right hW, zero_mul, dite_eq_right]
    rintro ⟨hWq, hJW, hWd⟩
    have : W.IsPrime := hWq.isPrime
    refine hW ⟨TopDimMinimal.full _ J W (d + Fintype.card K) hJW hJlt ?_, hWq.relevant⟩
    rw [hWd]
    exact lt_irrefl _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
