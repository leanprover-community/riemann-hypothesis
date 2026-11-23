module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper


open scoped Matrix.Norms.L2Operator in
theorem blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)

theorem blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)

end GlobalTheory.CompanionTheory.Unitary.ExpUpper
