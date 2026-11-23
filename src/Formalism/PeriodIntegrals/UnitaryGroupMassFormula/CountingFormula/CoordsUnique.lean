module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Coords

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem pb_coords (x : ι → V) (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) {v : V}
    (hv : v ∈ pbLat x 𝔞) : ∃ c : ι → K, (∀ i, c i ∈ 𝔞 i) ∧ v = ∑ i, c i • x i := by
  unfold pbLat at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, c, hc, rfl⟩ := hy
    refine ⟨Pi.single i c, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact hc
      · rw [Pi.single_eq_of_ne hj]
        exact (𝔞 j : Submodule (𝓞 K) K).zero_mem
    · symm
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  | zero => exact ⟨0, fun i => (𝔞 i : Submodule (𝓞 K) K).zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    exact ⟨c + d, fun i => (𝔞 i : Submodule (𝓞 K) K).add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
  | smul r y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨fun i => algebraMap (𝓞 K) K r * c i, fun i => ?_, ?_⟩
    · have hm := Submodule.smul_mem (𝔞 i : Submodule (𝓞 K) K) r (hc i)
      rwa [Algebra.smul_def] at hm
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, algebraMap_smul]

theorem coords_unique {x : ι → V} (hind : LinearIndependent K x) {c d : ι → K}
    (h : ∑ i, c i • x i = ∑ i, d i • x i) : c = d := by
  have h0 : ∑ i, (c - d) i • x i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have hz := Fintype.linearIndependent_iff.mp hind (c - d) h0
  funext i
  exact sub_eq_zero.mp (hz i)

end Coords

theorem sStable_prod {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} (s : Finset ι)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (h : ∀ i, SStable (𝔞 i)) : SStable (∏ i ∈ s, 𝔞 i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact sStable_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact sStable_mul (h j) ih

end PI.UnitaryGroupMassFormula.CntFormula.R6
