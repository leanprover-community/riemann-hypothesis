module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FinitePartAdelicPointMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussJ
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussO
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawD
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockMatrixDiagonalOneEqOne

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
