module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransportStatement

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

end GlobalTheory.CapelliSmooth
