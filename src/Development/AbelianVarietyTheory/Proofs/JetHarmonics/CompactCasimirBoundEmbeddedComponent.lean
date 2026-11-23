module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirLeTensorOperatorRaiseStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casKLe_io_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  intro M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise (N s) n ε (F s) M (Fin n) E
    (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s)
    (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n)
    (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _)
    (by
      intro a b _
      simp [Matrix.conjTranspose_single])
    (by
      intro x
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h1 : ∀ a b : Fin n,
          ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2 := by
        intro a b
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro j _ hj
            simp [Matrix.single, hj.symm]
          · simp
        · intro i _ hi
          simp [Matrix.single, hi.symm]
        · simp
      calc _ ≤ ∑ _a : Fin n, ∑ b : Fin n, ‖x b‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            split_ifs
            · exact (h1 a b).le
            · positivity
        _ = _ := by simp)
    (by
      intro a b _ j w
      have h := congrFun (hT.io_comm s a b w) j
      simp only [dualTens] at h
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [h, Finset.sum_eq_single a]
      · by_cases hj : j = b
        · subst hj
          simp
        · simp [hj, Matrix.single, Ne.symm hj]
      · intro i _ hi
        simp [Matrix.single, hi.symm]
      · simp)
    y hy d
  exact key

end GlobalTheory
