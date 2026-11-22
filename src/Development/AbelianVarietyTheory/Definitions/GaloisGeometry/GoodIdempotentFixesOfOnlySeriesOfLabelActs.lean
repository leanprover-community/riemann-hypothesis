module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

structure RowsB (D : D7) : Prop where
  rowSize : RowSize D
  a3 : SumRepresentations.adm3 D
  a4 : SumRepresentations.ArchimedeanSignatureMatching D
  thetaOne : ThetaOne D

structure RowsC (D : D7) : Prop where
  c4b : JointOccurrenceCondition D
  rho : GlobalDatumResidualRepCondition D
  dz : GlobalDatumDepthZeroCondition D
  parUp : ∀ i, ParUpRec D.nd D.naut i
  downMem : ∀ i, DownMemRec D.nd D.naut i
  goodPart : ∀ i, GoodPartRec D.nd D.naut i

def LamUsed (D : D7) : Prop :=
  ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ j : Fin D.R.m, LamPos D μ (j.1 + 1)

def GoodIdempotentFixesLocalisationForms (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par), ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
    D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F

def GoodIdempotentReadsAsGoodTypeProjector {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : Prop :=
  ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) y,
    X.R.extV j (X.tupT μ) y = X.fn hμ j f →
      (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f ↔ GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y)

theorem LamUsed.at {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem LamUsed.loc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  h.at (Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩)
    (D.nd.j_range i).1 (D.nd.j_range i).2

theorem goodIdempotentFixes_of_onlySeriesOfLabelActs {D : D7} (h : GlobalTheory.TypeLeaf.SerLoc D) : GoodIdempotentFixesLocalisationForms D := fun i σ' F hF hg =>
  (PlaceLabelTeichmuller.idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => h i σ' k v f F hF hf).1 hg

namespace Inputs

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D)
include I

end Inputs

end GlobalTheory.NRows

end
