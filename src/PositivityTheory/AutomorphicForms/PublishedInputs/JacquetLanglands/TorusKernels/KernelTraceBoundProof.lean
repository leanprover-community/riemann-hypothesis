module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
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

open scoped ENNReal NNReal

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_trace_bound_proof : UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : y ∈ D.LamF T γ
        · have hnf : γ ∈ {γ : PG F | ¬ Fix s γ} := fun hf => absurd (hγ s hs hf) (not_le.2 hsT)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hnf]
        · rw [Set.indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (le_of_lt (hT.trans hsT))
