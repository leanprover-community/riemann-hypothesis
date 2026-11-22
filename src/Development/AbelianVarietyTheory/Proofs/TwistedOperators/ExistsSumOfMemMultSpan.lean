module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def InK (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)

structure IsGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ τ g, InK M τ g → ∀ f ∈ A, rTr V (atTau θ V τ g) f ∈ A
  lie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f ∈ A, Rder θ V τ X f ∈ A

def IsIrrGKSub (A : Submodule ℂ (GA D V → ℂ)) : Prop :=
  IsGKSub θ M A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ (GA D V → ℂ), B ≤ A → IsGKSub θ M B → B = ⊥ ∨ B = A

def gkGen (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {A | ψ ∈ A ∧ IsGKSub θ M A}

theorem mem_gkGen (ψ : GA D V → ℂ) : ψ ∈ gkGen θ M ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isGKSub_gkGen (ψ : GA D V → ℂ) : IsGKSub θ M (gkGen θ M ψ) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => hA.2.lie τ X hX f (Submodule.mem_sInf.1 hf A hA)

theorem gkGen_le {ψ : GA D V → ℂ} {A : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ A) (hA : IsGKSub θ M A) :
    gkGen θ M ψ ≤ A :=
  sInf_le ⟨hψ, hA⟩

structure IsGKMult
    (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ)) : Prop where
  aut : ∀ u, IsAutFunSm θ V (F u)
  cusp : ∀ u, IsCuspFun V (F u)
  equivK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
    ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (w : M.H τ) = M.rep τ g (u τ) → F (Function.update u τ w) = rTr V (atTau θ V τ g) (F u)
  equivLie : ∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
      F (Function.update u τ w) = Rder θ V τ X (F u)

def multSpan : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {f | ∃ (F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)) (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), IsGKMult θ M F ∧ f = F u}

def IsKFinCuspOfType (f : GA D V → ℂ) : Prop :=
  IsAutFunSm θ V f ∧ IsCuspFun V f ∧ (∀ τ, IsTypeAt θ V τ (S τ) f) ∧
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ f ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W

theorem IsGKMult.smul {F : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
    (GA D V → ℂ)} (h : IsGKMult θ M F) (c : ℂ) : IsGKMult θ M (c • F) := by
  constructor
  · intro u
    exact Formalism.IndefR.Mult.isAutFunSm_smul θ V (h.aut u) c
  · intro u
    exact Formalism.IndefR.Mult.isCuspFun_smul V (h.cusp u) c
  · intro τ g hg hk u w hw
    rw [smul_apply, smul_apply, h.equivK τ g hg hk u w hw]
    rfl
  · intro τ X hX u w hw
    rw [smul_apply, smul_apply, h.equivLie τ X hX u w hw,
      Formalism.IndefR.Mult.rder_smul]

theorem exists_sum_of_mem_multSpan {ψ : GA D V → ℂ} (hψ : ψ ∈ multSpan θ M) :
    ∃ (n : ℕ) (F : Fin n → MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ))
      (GA D V → ℂ)) (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, IsGKMult θ M (F l)) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  obtain ⟨n, c, f, hf⟩ := Submodule.mem_span_set'.1 hψ
  choose F u hF hFu using fun i => (f i).2
  refine ⟨n, fun l => c l • F l, u, fun l => (hF l).smul θ M (c l), fun g => ?_⟩
  rw [← hf, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hFu l]
  rfl

end GlobalTheory.CuspGK

end
