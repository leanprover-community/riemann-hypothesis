import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnTwoPowMul
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.DedekindResidueLeOfAdmitted
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDAll
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.NearCountOfLayers

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_eps (X : CData) (cε : ℝ) : ℝ := Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f

def GeoS (X : CData) (cε Cv Cd Cq : ℝ) : Prop :=
  ∃ (S : CSize X) (volK : ℝ), S.Strata ∧ S.Density ∧ S.KappaVol Cv ∧
    S.NearLayers (cn_eps X cε) (3 * Real.sqrt ((X.I.n : ℝ) * cn_eps X cε)) ∧ S.SepStep ∧
    (1 ≤ X.qq → S.DeepStepsQ volK Cd Cq)

def GeoC (X : CData) (Cres cε Cv Cd Cq : ℝ) : Prop := cn_ResBound X Cres ∧ GeoS X cε Cv Cd Cq







def StepsG (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.OpExists ∧ X.KernelDiag ∧ X.FinVol ∧ X.LowProj ∧ GeoS X cε Cv Cd Cq

def StepsG'' (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.RegRep ∧ X.KernelDiag ∧ X.FinVol ∧ GeoS X cε Cv Cd Cq


def UniformGeometricFacts : Prop :=
  ∃ cε Cv Cd Cq : ℝ, 0 < cε ∧ cε ≤ 1 / 90000 ∧ 1 ≤ Cv ∧ 1 ≤ Cd ∧ 0 ≤ Cq ∧ 16 * Cq ≤ Cd ∧ ∀ cb Cres A Cb : ℝ, 0 < cb → 1 ≤ A →
    ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ n₀' ≥ n₀, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7,
      (ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D) → DiscreteSeriesDecayBound D → Conclusion2 D n₀' A Cb →
        StepsG n₀' A C cb cε Cv Cd Cq


end Formalism.MainNotions.LeviCoordinates

end
