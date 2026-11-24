module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Lagrange
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.Spectrum

@[expose] public section

open Matrix

namespace GlobalTheory


open scoped Matrix.Norms.L2Operator in
theorem unitary_submonoid_exists_skewAdjoint_log_polynomial (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ)
    (hk : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      star X = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  classical
  have hspec := spectrum.subset_circle_of_unitary (𝕜 := ℂ) hk
  have hfin := Matrix.finite_spectrum k
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) := fun f => hfin.continuousOn f
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z ∈ spectrum ℂ k, p.eval z = Complex.log z := by
    refine ⟨Lagrange.interpolate hfin.toFinset id Complex.log, fun z hz => ?_⟩
    have := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) (i := z) Complex.log
      (Set.injOn_id _) (by simpa using hz)
    simpa using this
  refine ⟨cfc Complex.log k, p, ?_, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 : ‖z‖ = 1 := by simpa using hspec hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  · rw [← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp Complex.exp Complex.log k
      (hg := (Set.Finite.image _ hfin).continuousOn _) (hf := hcont _)]
    have h0 : ∀ z ∈ spectrum ℂ k, (Complex.exp ∘ Complex.log) z = id z := by
      intro z hz
      have h1 : ‖z‖ = 1 := by simpa using hspec hz
      have : z ≠ 0 := by rintro rfl; simp at h1
      simp [Complex.exp_log this]
    rw [cfc_congr h0, cfc_id ℂ k]
  · rw [← cfc_polynomial p k]
    exact cfc_congr fun z hz => (hp z hz).symm

theorem unitary_exists_skew_log (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) :
    ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ),
      Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  have hmem : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨hk, mul_eq_one_comm.mp hk⟩
  obtain ⟨X, p, h1, h2, h3⟩ := unitary_submonoid_exists_skewAdjoint_log_polynomial n k hmem
  exact ⟨X, p, h1, h2, h3⟩

end GlobalTheory
