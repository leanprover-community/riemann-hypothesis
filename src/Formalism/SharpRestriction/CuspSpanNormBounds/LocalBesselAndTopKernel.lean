module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.HermitianLattices.StatementMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LocalBesselAndTopKernel.TOP

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

end Formalism.MainNotions.LocalBesselAndTopKernel.TOP

namespace Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

end Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

namespace Formalism.MainNotions.LocalBesselAndTopKernel.SW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end Ext

open Formalism.BasicNotions

end Formalism.MainNotions.LocalBesselAndTopKernel.SW

namespace Formalism.MainNotions.LocalBesselAndTopKernel

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def projection_sandwich_lattice (D : D7) : Prop :=
  UnitaryVolumeMass.cTvA D

def MassRatio₂ (D : D7) (C1 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvB D C1

def kernel_index_full_lattice (D : D7) (C2 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvC D C2

def gram_det_kernel_dual_lattice (D : D7) (C3 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvD D C3

def MidVolumeChain (D : D7) (large₂ : SizeData₂ D) (ep0 CV : ℝ) : Prop :=
  UnitaryVolumeMass.cTvG D large₂ ep0 CV

def AdmittedWeylDimension : Prop :=
  ∀ (k' : ℕ) (u : Fin k' → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k') (Fin k') ℂ → (H →L[ℂ] H)), StrictAnti u → IsHCTypeU k' u π →
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k', (i.factorial : ℝ)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  ∀ i : ℕ, 3 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def cardGL (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (q ^ n - q ^ i)

def dimNS (D : D7) : ℕ := D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)

def idxRows (D : D7) : ℝ :=
  ∏ᶠ p ∈ typedPl D, cardGL (Ideal.absNorm p.asIdeal : ℝ) D.R.r /
    ((Ideal.absNorm p.asIdeal : ℝ) ^ dimNS D * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))

def FamilyMidVolume (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (L : Submodule (𝓞 D.host.E) V), h.IsSymm →
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word,
      (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * gaG D *
        (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f) ∧
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r →
      D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * idxRows D * ∏ τ, D.dsig τ)

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card
def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

section Glob

open Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7}

variable (D)

variable {D}

variable (D)

end Glob

section One

open Formalism.MainNotions.S.LocalSplitGroups

def FamilyExpansionSecond (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  FamilySchurFormalDegree D → GL5LogLValueBoundByZeta D → FamilyMidVolume D → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D
def SecondBoundHyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C1 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MassRatio₂ D C1
def LocalTiedPairs (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MidVolumeChain D large₂ ep0 CV → gram_det_kernel_dual_lattice D C3'

end One

section Family

open Formalism.MainNotions.S.LocalSplitGroups

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def UnderF (C0 Cg cb Cu cT CT : ℝ) (P : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P (Fm.D x i) (Fm.L x i)

def SecondSizeStatement : Prop := ∀ x (i : Fm.Ix x), FamilySchurFormalDegree (Fm.D x i)
def BesselFormLine : Prop := ∀ x (i : Fm.Ix x), GL5LogLValueBoundByZeta (Fm.D x i)
def FamilyRanksHypothesis (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => FamilyMidVolume D

def FamilyBesselBoundFirstPart (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => projection_sandwich_lattice D
def TheoremThreePassage (C0 Cg cb Cu cT CT C1 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => MassRatio₂ D C1
def FamilyLowestKType (C0 Cg cb Cu cT CT C2 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => kernel_index_full_lattice D C2
def LocalSplitExponents (C0 Cg cb Cu cT CT C3' : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => gram_det_kernel_dual_lattice D C3'
def FamilyTopBound (C0 Cg cb Cu cT CT ep0 CV : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D large₂ => MidVolumeChain D large₂ ep0 CV

def FamilyUnfoldingCount (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  SecondSizeStatement Fm → BesselFormLine Fm → FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT → FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT

end Family

section Closed

open Formalism.MainNotions.S.LocalSplitGroups

end Closed

end Formalism.MainNotions.LocalBesselAndTopKernel
