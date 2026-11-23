module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.LeviChart

variable {D : D7}

theorem rat_Tm (A : HSp D) (μ : D.host.E) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (dblDec A).jX (incA D μ • (dblDec A).jY)).submatrix id finSumFinEquiv.symm := by
  ext i j
  rcases h : finSumFinEquiv.symm j with k | k <;>
    simp [rat, Tm, HypDec.jX, HypDec.jY, Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, h]

theorem doubledBasisSkewColumnMatrix_adelic_mul_blockDiagonal (A : HSp D) (μ : D.host.E) (a d : Mx D A.rank A.rank) :
    (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) * blk4 a 0 0 d =
      (Matrix.fromCols ((dblDec A).jX * a) ((incA D μ • (dblDec A).jY) * d)).submatrix id finSumFinEquiv.symm := by
  rw [rat_Tm, blk4, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem mul_Tm (A : HSp D) (μ : D.host.E) (M : Mx D (A.rank + A.rank) (A.rank + A.rank)) :
    M * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (Matrix.fromCols (M * (dblDec A).jX) (M * (incA D μ • (dblDec A).jY))).submatrix id finSumFinEquiv.symm := by
  rw [rat_Tm, ← Matrix.mul_fromCols, Matrix.submatrix_mul _ _ id id _ Function.bijective_id, Matrix.submatrix_id_id]

end GlobalTheory.StdUnn.LeviChart


open GlobalTheory.StdUnn.LeviChart in
theorem GlobalTheory.StdUnn.chart_levi : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (g : GA D (dblSp A)) (a : GL (Fin A.rank) (AE D)), mat (κ g) = blk4 a.1 0 0 (adj (a⁻¹).1) → g = (dblDec A).levi a := by
  intro D A μ hμ κ hκ g a hg
  have h := hκ g
  rw [hg, doubledBasisSkewColumnMatrix_adelic_mul_blockDiagonal, mul_Tm] at h
  have h' := congrArg (fun M : Mx D _ _ => M.submatrix id finSumFinEquiv) h
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  obtain ⟨hX, hY⟩ := Matrix.fromCols_inj h'
  have hc : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ.1, map_one]
  refine (dblDec A).ga_ext ?_ ?_ ?_
  · rw [HypDec.levi_jX, hX]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [HypDec.levi_jY]
    have h2 := congrArg (fun M => incA D μ⁻¹ • M) hY
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul] at h2
    exact h2.symm

end
