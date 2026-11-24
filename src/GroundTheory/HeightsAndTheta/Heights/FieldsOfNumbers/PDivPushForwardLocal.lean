module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForwardLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u}
    [Field F] {W : Ideal (MRing ι F)} (hW : IsMultiProjPrime W) (c : K → ℕ) :
    ∃ h : MRing ι F, IsMultiHomog h c ∧ h ∉ W := by
  choose v hv using hW.relevant
  have := hW.isPrime
  refine ⟨∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (c k))
    have hc : (∑ k, c k • blockWeight ι ⟨k, v k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem this _ hk)

theorem DivPushForwardLocal.proof (h1 : DivCycleMinimal.Statement.{u})
    (h2 : ConeLocalLength.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : SemilocalFiniteRank.Statement.{u}) (h5 : SemilocalLength.Statement.{u}) :
    DivPushForwardLocal.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hdim hdimP c a ha haP W hW hWd M hM1 hM0
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  by_cases hPW : contractPrime j P' ⊔ Ideal.span {a} ≤ W
  · have := hW.isPrime
    have hPle : contractPrime j P' ≤ W := le_trans le_sup_left hPW
    obtain ⟨h, hh, hhW⟩ := exists_form_not_mem hW c
    let α : degZeroLoc (contractPrime j P') {W} := ⟨_, div_mem_degZeroLoc _ _ ha hh
      (fun hm => hhW (hPle hm)) (fun W₁ h₁ => (Set.mem_singleton_iff.mp h₁) ▸ hhW)⟩
    have hα0 : α ≠ 0 := by
      intro h0
      have h0' := congrArg Subtype.val h0
      rcases div_eq_zero_iff.mp h0' with h' | h' <;>
        rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
      · exact haP h'
      · exact hhW (hPle h')
    obtain ⟨⟨hNo, hLo⟩, hdA⟩ := h3 F K _ _ hP W hW hPle
    obtain ⟨hfin, htf, hrk⟩ := h4 F K K' j ι' P' hP' n hdim hdimP W hW hWd hPle
    have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (degZeroLoc P' (fibrePrimes j P' W)) α
      (hdA n hdimP hWd) hα0
    obtain ⟨N, hN, hMN⟩ := h5 F K K' j ι' P' hP' n hdim hdimP c a h ha hh haP W hW hWd hPle hhW
      M hM1 hM0 α rfl
    obtain ⟨hmin, hfinm⟩ := h1 F K _ _ hP.isPrime n hdimP a haP W hW.isPrime hWd hPW
    have hcone := h2 F K _ _ hP W hW hPle c a h ha hh hhW α rfl
    have hdc : divCycle (contractPrime j P') a W =
        ((multAt (contractPrime j P' ⊔ Ideal.span {a}) W).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hW.relevant⟩]
    rw [hMN, hdc]
    rw [hN, hrk, ← hcone] at key
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinm
    rw [← hm] at key ⊢
    have hNm : N = relDeg j P' * m := by exact_mod_cast key
    rw [hNm, ENat.toNat_natCast]
    push_cast
    rfl
  · have hR : divCycle (contractPrime j P') a W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact hPW h.1.2
    rw [hR, mul_zero]
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    by_cases hD : divCycle P' (rename (blockIncl j ι') a) W' = 0
    · rw [hD, zero_mul]
    · refine mul_eq_zero_of_right _ (hM0 W' fun hc => hPW ?_)
      unfold divCycle at hD
      split_ifs at hD with hm
      · rw [← hc]
        refine sup_le (Ideal.comap_mono (le_trans le_sup_left hm.1.1.2)) ?_
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hm.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      · exact absurd rfl hD

end

end GroundTheory.Heights₂.Heights.FieldNumbers
