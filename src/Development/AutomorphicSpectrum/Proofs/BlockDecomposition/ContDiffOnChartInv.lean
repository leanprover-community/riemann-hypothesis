module

import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.InvContDiffOn
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

namespace GlobalTheory.CompanionTheory.MatInv

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_chartInv (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chart n).symm (Ring.inverse (chart n M)))
      {M | IsUnit (chart n M)} := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact ((GlobalTheory.CompanionTheory.MatInv.chart n).symm.contDiff.contDiffAt.comp M
    (h1.comp M (GlobalTheory.CompanionTheory.MatInv.chart n).contDiff.contDiffAt)).contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiffOn_inv : ∀ {n : ℕ}, ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  apply PositivityTheory.RgBcC.LfSt.Kchain.KcInv.inv_contDiffOn <;> assumption

end GlobalTheory.CompanionTheory.MatInv
