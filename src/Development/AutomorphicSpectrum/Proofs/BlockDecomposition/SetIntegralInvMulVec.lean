module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitriangularMapInduction
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inv_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (m : ℕ) (g : GL (Fin m) k) (M : Set (Fin m → k))
    (F : (Fin m → k) → ℂ) :
    ∫ x in M, F (((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x) ∂(piHaar ν m) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
        ∫ y in {y | (g : Matrix (Fin m) (Fin m) k) *ᵥ y ∈ M}, F y ∂(piHaar ν m) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hinv : ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) * (g : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.inv_mul g
  have hinv' : (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.mul_inv g
  let e : (Fin m → k) ≃ᵐ (Fin m → k) :=
    { toFun := fun x => (g : Matrix (Fin m) (Fin m) k) *ᵥ x
      invFun := fun x => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x
      left_inv := fun x => by simp only [mulVec_mulVec, hinv, one_mulVec]
      right_inv := fun x => by simp only [mulVec_mulVec, hinv', one_mulVec]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have he : MeasurableEmbedding (Matrix.mulVec (g : Matrix (Fin m) (Fin m) k)) :=
    e.measurableEmbedding
  have hμ := GlobalTheory.UnipChange.smul_map_mulVec_pi ν (g : Matrix (Fin m) (Fin m) k)
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.val_det_apply g)
  unfold GlobalTheory.CompanionTheory.MirPair.piHaar GlobalTheory.SplitWeil.nabs
  conv_lhs => rw [← hμ]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul,
    he.restrict_map, he.integral_map]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mulVec_mulVec, hinv, one_mulVec]

end GlobalTheory.CompanionTheory.MirPair
