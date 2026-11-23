module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExpSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = 1 + N :=
  _root_.UpperTheory.Reformulated.B.Qf11.expSq N h

theorem UpperTheory.V.AlgRepEndIrreducible.expGenC :
    ∀ (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ)), (∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, g.det ≠ 0 → g ∈ H := by
  intro n H hH g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
      exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2
    funext i
    rw [Pi.exp_def]
    simp only [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this
    exact this
  · intro A B _ _ hA hB
    exact H.mul_mem hA hB
