module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem ggMatrixBound_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hC : ConvScalar) (hR : GenericRatio) : GGMatrixBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef
  have hherm : A.IsHermitian := hH ι Fq k ψ X
  have hspec := hS X A _ hherm (fun w μ hw hAw =>
    hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw
      (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)

end PI.GGMatBoundW
