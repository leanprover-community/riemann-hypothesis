module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

def twoPYLin (p q : ℕ) : (Fin p → Fin q → ℂ) →ₗ[ℝ] Mat p q where
  toFun C := pY C + pY C
  map_add' B C := by rw [pY_add]; abel
  map_smul' t B := by rw [pY_smul, smul_add]; rfl

def entryLin {p q : ℕ} (a b : Ix p q) : Mat p q →ₗ[ℝ] ℂ where
  toFun M := M a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Matrix.Norms.Operator in
theorem contDiff_exp_two_pY_entry (p q : ℕ) (a b : Ix p q) :
    ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => NormedSpace.exp (pY C + pY C) a b) := by
  have h1 : ContDiff ℝ 1 (NormedSpace.exp : Mat p q → Mat p q) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have h2 : ContDiff ℝ 1 (fun C : Fin p → Fin q → ℂ => (pY C + pY C : Mat p q)) :=
    (LinearMap.toContinuousLinearMap (twoPYLin p q)).contDiff
  have h3 : ContDiff ℝ 1 (fun M : Mat p q => M a b) :=
    (LinearMap.toContinuousLinearMap (entryLin a b)).contDiff
  exact h3.comp (h1.comp h2)

theorem hasStrictFDerivAt_exp_two_pY : ∀ (p q : ℕ) (B : Fin p → Fin q → ℂ), (∀ (V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • V) a b) ((NormedSpace.exp (pY B) * sAd (pY B) V * NormedSpace.exp (pY B)) a b) 0) → ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B) := by
  intro p q B h
  have hc : ContDiff ℝ 1 (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) =>
      NormedSpace.exp (pY C + pY C) a b) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_exp_two_pY_entry p q a b
  have hs := hc.contDiffAt.hasStrictFDerivAt_fderiv (x := B) (by simp)
  refine ⟨_, hs, fun C => ?_⟩
  ext a b
  have hl : HasDerivAt (fun t : ℝ => B + t • C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const C).const_add B
  have h1 := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h1 a) b
  have h3 := h (pY C + pY C) a b
  have e : (fun t : ℝ => NormedSpace.exp (pY B + pY B + t • (pY C + pY C)) a b) =
      fun t : ℝ => NormedSpace.exp (pY (B + t • C) + pY (B + t • C)) a b := by
    funext t
    have e' : pY B + pY B + t • (pY C + pY C) = pY (B + t • C) + pY (B + t • C) := by
      rw [pY_add, pY_smul, smul_add]; abel
    rw [e']
  rw [e] at h3
  exact h2.unique h3

end GlobalTheory.PolarU
