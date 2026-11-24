module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
