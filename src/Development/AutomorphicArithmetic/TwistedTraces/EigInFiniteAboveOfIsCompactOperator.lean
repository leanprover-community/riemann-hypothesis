module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.CompactSelfAdjoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigIn_finite_above_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∀ η : ℝ, 0 < η → {x : ℝ | η < x ∧ eigIn W A x ≠ ⊥}.Finite ∧ ∀ x : ℝ, η < x → FiniteDimensional ℂ (eigIn W A x) := by
  intro H _ _ _ W A hW hA hAW hC η hη
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : ∀ v, prj W v ∈ W := by
    intro v
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ v, ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro v w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hfix : ∀ w ∈ W, prj W w = w := by
    intro w hw
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (W.le_topologicalClosure hw) ?_
    simp
  have hmem : ∀ x : ℝ, ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro x w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hB : IsSelfAdjoint (A ∘L prj W) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    have h1 : inner ℂ (A (prj W u)) v = inner ℂ (A (prj W u)) (prj W v) := by
      have := hperp v _ (hAW _ (hPW u))
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : inner ℂ u (A (prj W v)) = inner ℂ (prj W u) (A (prj W v)) := by
      have := hperp u _ (hAW _ (hPW v))
      rw [inner_sub_right, sub_eq_zero] at this
      rw [← inner_conj_symm, this, inner_conj_symm]
    rw [h1, h2]
    exact hA.isSymmetric _ _
  have hle : ∀ x : ℝ, eigIn W A x ≤
      Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ) := by
    intro x w hw
    obtain ⟨hwW, hwA⟩ := (hmem x w).1 hw
    rw [Module.End.mem_eigenspace_iff]
    change A (prj W w) = _
    rw [hfix w hwW, hwA]
  have hfin := GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge hC hB hη
  refine ⟨?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_)
      (Complex.ofReal_injective.injOn)
    rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hle x hw, hw0⟩
    · have : η ≤ |x| := hx.le.trans (le_abs_self x)
      simpa using this
  · intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      have : x ≠ 0 := (hη.trans hx).ne'
      exact_mod_cast this
    haveI : FiniteDimensional ℂ (Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hC _ hx0
    exact Submodule.finiteDimensional_of_le (hle x)
