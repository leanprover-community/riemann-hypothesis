module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCoeffs

theorem exists_coeff_matrices_of_span_eq {K : Type} [Field K] {n r : ℕ}
    (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c)
    (hs : Submodule.span K (Set.range c) = Submodule.span K (Set.range C)) :
    ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
      C = T * c ∧ c = L * C ∧ L * T = 1 := by
  have hT0 : ∀ j, ∃ t : Fin r → K, ∑ i, t i • c i = C j := by
    intro j
    have hj : C j ∈ Submodule.span K (Set.range c) := by
      rw [hs]
      exact Submodule.subset_span (Set.mem_range_self j)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hj
  have hL0 : ∀ i, ∃ t : Fin n → K, ∑ j, t j • C j = c i := by
    intro i
    have hi : c i ∈ Submodule.span K (Set.range C) := by
      rw [← hs]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact (Submodule.mem_span_range_iff_exists_fun K).mp hi
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin r) K, ∀ j, ∑ i, T j i • c i = C j :=
    ⟨fun j => (hT0 j).choose, fun j => (hT0 j).choose_spec⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) K, ∀ i, ∑ j, L i j • C j = c i :=
    ⟨fun i => (hL0 i).choose, fun i => (hL0 i).choose_spec⟩
  have hCT : C = T * c := by
    ext j k
    rw [← hT j, Matrix.mul_apply]
    simp [Finset.sum_apply]
  have hcL : c = L * C := by
    ext i k
    rw [← hL i, Matrix.mul_apply]
    simp [Finset.sum_apply]
  refine ⟨T, L, hCT, hcL, ?_⟩
  have hLT : L * T * c = c := by rw [Matrix.mul_assoc, ← hCT, ← hcL]
  have hz0 : (L * T - 1) * c = 0 := by rw [Matrix.sub_mul, hLT, Matrix.one_mul, sub_self]
  have hc' := Fintype.linearIndependent_iff.mp hc
  ext i0 i
  have hrow : ∑ i, (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i • c i = 0 := by
    funext k
    have h0 := congrFun (congrFun hz0 i0) k
    rw [Matrix.mul_apply] at h0
    simpa [Finset.sum_apply] using h0
  have h1 : (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i = 0 := hc' (fun i => (L * T - 1 : Matrix (Fin r) (Fin r) K) i0 i) hrow i
  rwa [Matrix.sub_apply, sub_eq_zero] at h1

end GlobalTheory.CompanionTheory.BruhatCoeffs
