module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1

        simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
