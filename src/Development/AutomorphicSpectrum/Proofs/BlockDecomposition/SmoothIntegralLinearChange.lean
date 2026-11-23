module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm
import GroundTheory.AutomorphicForms.MeasuresModulus
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntHaar

open MeasureTheory

variable {k : Type} [Field k]

def glLinearEquiv {t : ℕ} (w : GL (Fin t) k) : (Fin t → k) ≃ₗ[k] (Fin t → k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k))
    (Matrix.toLin' ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem coe_glLinearEquiv_symm {t : ℕ} (w : GL (Fin t) k) :
    ((glLinearEquiv w).symm : (Fin t → k) → (Fin t → k)) =
      ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec := by
  funext v
  rfl

theorem det_glLinearEquiv {t : ℕ} (w : GL (Fin t) k) :
    LinearEquiv.det (glLinearEquiv w) = Matrix.GeneralLinearGroup.det w := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (w : Matrix (Fin t) (Fin t) k)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_inv_mulVec (t : ℕ) [m : MeasurableSpace (Fin t → k)] [hb : BorelSpace (Fin t → k)]
    (μ : Measure (Fin t → k)) [μ.IsAddHaarMeasure] (w : GL (Fin t) k) :
    μ.map ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ := by
  borelize k
  have hp : @BorelSpace (Fin t → k) _ MeasurableSpace.pi := Pi.borelSpace
  have e : m = MeasurableSpace.pi := hb.measurable_eq.trans hp.measurable_eq.symm
  subst e
  rw [← coe_glLinearEquiv_symm, ← det_glLinearEquiv]
  exact GlobalTheory.ChangeVarPi.map_symm_eq_smul k (Fin t) μ (glLinearEquiv w)

theorem smInt_comp_inv_mulVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  intro k _ _ _ _ t _ _ μ _ Z _ _ w φ hl _
  have hc : Continuous ((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec :=
    continuous_const.matrix_mulVec continuous_id
  have hval : ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) =
      (((distribHaarChar k (Matrix.GeneralLinearGroup.det w) : NNReal) : ℝ) : ℂ) := by
    rw [detChar_apply, val_absPow, Complex.cpow_one]
    rfl
  rw [hval]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  have hlev : μ ((fun x => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec x)) ⁻¹' {v}) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det w)) • μ (φ ⁻¹' {v}) := by
    rw [← Measure.smul_apply, ← map_inv_mulVec t μ w]
    exact (Measure.map_apply hc.measurable (hl.isOpen_fiber v).measurableSet).symm
  rw [hlev, ENNReal.toReal_smul, smul_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul]

end GlobalTheory.CompanionTheory.Rodier.SmIntHaar

end
