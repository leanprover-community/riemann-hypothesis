module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
