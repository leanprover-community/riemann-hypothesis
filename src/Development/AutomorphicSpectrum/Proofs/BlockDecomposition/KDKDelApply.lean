module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
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

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Kabs

theorem kD_kDel_apply {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_

  rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]

end GlobalTheory.CompanionTheory.Kabs
