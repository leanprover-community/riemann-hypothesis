import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusGluing

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open Formalism.BasicNotions Formalism.MainNotions.S.Lat NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LatS (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev FlS (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

def adm1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stGlueDisc D

def adm2 (_D : D7) : Prop :=
  S.UnitaryVolumeMass.stBRhad

def adm3 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stKron D

def Conclusion1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem1 D

def Conclusion2 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem2 D

def PointsLemma (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmA D

def Conclusion4 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmB D

def DefiniteComplementAndPairRank (D : D7) : Prop :=
  (∀ (u : D.what₂.Word) (T' : ℕ) (Λ : LatS D) (F : FlS D (Tu D u)) (F' : FlS D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → DefiniteComplementRank D Λ F F') ∧
  (∀ (u : D.what₂.Word) (T' : ℕ) (Λ : LatS D) (F : FlS D (Tu D u)) (F' F'' : FlS D T')
    (β : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) →
      (2 ≤ s0 Λ F F' F'' β D.R.k →
        ∀ W : Submodule D.host.E (hS D).V, WHyp D F W → LatticeSpanEquality D Λ (gS D) F F' F'' β W) ∧
      (s0 Λ F F' F'' β D.R.k = 1 → HyperplaneEquality D Λ F F' F'' β))

def GlobalIntegralModelCondition (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteComplementAllWords D

def HyperplaneRank (D : D7) : Prop :=
  S.UnitaryVolumeMass.HyperplaneRankAllWords D

def DefiniteRankOne (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteRankOneAllWords D


def aux₃ (D : D7) : Prop := Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D

def admitted (D : D7) : Prop := adm1 D ∧ adm2 D ∧ adm3 D

def Stmt (D : D7) : Prop := admitted D → aux₃ D

def SettingFromHypotheses (D : D7) : Prop := admitted D → DefiniteComplementAndPairRank D

def GluingBaseStatement (D : D7) : Prop := GlobalIntegralModelCondition D

def IntegralityFromMetric (D : D7) : Prop := adm1 D → GlobalIntegralModelCondition D → Conclusion1 D

def HodgeTateFromSandwich (D : D7) : Prop := Conclusion2 D

def PrvA2OfGlobalModelA0Cond (D : D7) : Prop := GlobalIntegralModelCondition D → HyperplaneRank D

def TowerRallisLemma (D : D7) : Prop := adm2 D → Conclusion1 D → Conclusion2 D → HyperplaneRank D → PointsLemma D

def ConditionalHyperplaneRank (D : D7) : Prop := GlobalIntegralModelCondition D → DefiniteRankOne D

def ThetaChernBoundOfLastLine (D : D7) : Prop := adm1 D → adm3 D → Conclusion2 D → DefiniteRankOne D → Conclusion4 D


def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)
def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)
def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF1 Fm ∧ admF2 Fm ∧ admF3 Fm

def ConclusionF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i)
def ConclusionF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i)
def ConclusionF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), PointsLemma (Fm.D x i)
def FamilyEstimateFour {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Conclusion4 (Fm.D x i)
def FamilyDefiniteComplementAndPairRank {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DefiniteComplementAndPairRank (Fm.D x i)
def FamilyGluingBaseEveryMember {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), GlobalIntegralModelCondition (Fm.D x i)
def FamilyDefiniteRankEveryMember {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), HyperplaneRank (Fm.D x i)
def FamilyHyperplaneRank {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DefiniteRankOne (Fm.D x i)
def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ConclusionF1 Fm ∧ ConclusionF2 Fm ∧ ConclusionF3 Fm ∧ FamilyEstimateFour Fm

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → OrbitValuationBound Fm

def ConditionalFamilyDefiniteComplementAndPairRank {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → FamilyDefiniteComplementAndPairRank Fm

def FamilyGluingBaseStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyGluingBaseEveryMember Fm
def PeriodFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF1 Fm → FamilyGluingBaseEveryMember Fm → ConclusionF1 Fm
def DeterminantValueFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ConclusionF2 Fm
def ConditionalFamilyDefiniteRank {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyGluingBaseEveryMember Fm → FamilyDefiniteRankEveryMember Fm
def FlatLineDegreeFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  admF2 Fm → ConclusionF1 Fm → ConclusionF2 Fm → FamilyDefiniteRankEveryMember Fm → ConclusionF3 Fm
def ConditionalFamilyHyperplaneRank {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyGluingBaseEveryMember Fm → FamilyHyperplaneRank Fm
def LiftNormFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  admF1 Fm → admF3 Fm → ConclusionF2 Fm → FamilyHyperplaneRank Fm → FamilyEstimateFour Fm


end Formalism.MainNotions.VanishingOnXAndXPlusGluing

end
