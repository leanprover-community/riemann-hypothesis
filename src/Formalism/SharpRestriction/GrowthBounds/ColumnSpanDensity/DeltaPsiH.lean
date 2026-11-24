module

public import Formalism.PolynomialDimension.StatementHar
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))

def PsiXY (K : Type) [Field K] (m : ℕ) : PolXY K (m + 1) →ₐ[K] MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K :=
  aeval (Sum.elim (fun i : Fin (m + 1) => X (true, (i, (0 : Fin (m + 1)))))
    (fun i : Fin (m + 1) => rename (Prod.mk false) (covY K m i)))

def deltaB (K : Type) [Field K] (m : ℕ) :
    MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) K →ₐ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  rename Prod.snd

theorem sum_covY (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) :
    ∑ i : Fin (m + 1), (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) * covY K m i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) :=
    Matrix.of fun a c => Fin.cases (X (a, 0)) (fun b : Fin (k + 1) => X (a, b.castSucc)) c
  have h0 : N.det = 0 :=
    Matrix.det_zero_of_column_eq (i := 0) (j := (0 : Fin (k + 1)).succ) (Fin.succ_ne_zero 0).symm
      (fun a => rfl)
  rw [Matrix.det_succ_column_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : N.submatrix i.succAbove Fin.succ =
      fun a b => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 2) × Fin (k + 2)) K) := by
    ext a b
    simp [N]
  have hN0 : N i 0 = X (i, 0) := by simp [N]
  rw [hsub, hN0, covY]
  ring

theorem delta_Psi_h (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) : deltaB K m (PsiXY K m (hXY K (m + 1))) = 0 := by
  have hid : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
  have h1 : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i) * X (Sum.inr i))) =
      X (i, 0) * covY K m i := by
    intro i
    simp only [PsiXY, deltaB, map_mul, aeval_X, Sum.elim_inl, Sum.elim_inr, rename_X, rename_rename, hid,
      rename_id, AlgHom.id_apply]

  rw [hXY, map_sum, map_sum, Finset.sum_congr rfl fun i _ => h1 i]
  exact sum_covY K m hm

end Formalism.MainNotions.flipOneThree.Pf

end
