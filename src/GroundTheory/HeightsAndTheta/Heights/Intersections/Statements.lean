module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def DegreeGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
      ptsIntegral P (pot L) (fun _ => 1) =
        NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (fun j => (L j).a)

theorem isArithVar_projLine : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := by
  refine ⟨inferInstance, ⟨Ideal.isPrime_bot,
    ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun _ => ⟨0, by rw [Submodule.mem_bot]; exact X_ne_zero _⟩⟩, ?_, ?_⟩
  · ext a
    simp [Ideal.mem_comap]
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    have hc : Nat.card ((_ : Unit) × PBlk 2 ()) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [ENat.card_eq_coe_natCard, hc, Fintype.card_unit]
    rfl

theorem isSmoothHerm_fsLine (n : ℕ) : IsSmoothHerm (fsLine n) := by
  have hfun : (fsLine n).h = fun z => ∏ k : Unit, Real.sqrt (∑ i : Fin n, ‖z ⟨k, i⟩‖ ^ 2) := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, Pi.one_apply, zpow_one,
      EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.sqrt ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, PBlk n k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

end

end GroundTheory.Heights₂.Heights.Inter
