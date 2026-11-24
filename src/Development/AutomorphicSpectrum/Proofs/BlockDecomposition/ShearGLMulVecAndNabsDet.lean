module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
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

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
