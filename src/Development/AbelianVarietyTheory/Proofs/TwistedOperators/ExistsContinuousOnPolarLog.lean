module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
