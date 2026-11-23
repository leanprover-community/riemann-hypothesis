module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingDataStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSumsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvaluesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabelsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeActionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHeckeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTameStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSectionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.PendClose

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) →
    SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D →
    SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  intro D M hT hR hA hPar h0 h5 hIne hDep hGen hZL hCI hCT hSer hZeta hDZ hAdm
  have hSU : GlobalTheory.EtaJoin.SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hSec : ∀ i, Nonempty (Sec D i) := fun i =>
    GlobalTheory.T.nonempty_localised_forms_type_section_hecke D M i hT hR hA hSU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M hT hA i)
  obtain ⟨lz, hlz⟩ := GlobalTheory.T.exists_finiteGroupData_seriesIdempotentsLabelSums D
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.T.exists_label_inertia_eigenvalues D hIne hDep hGen
  have hChar : LabChar D := GlobalTheory.T.labelTwistMultipliesRoots_of_tame_labels D h0 hIne hDep hGen
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_groupAlgebraCentreLatticeAction D hSec hZL hCI hCT
  have hPr : PrType D := GlobalTheory.T.typeSpaceProjectionEigen_of_localisedFormsSection D hSec
  have hSplit : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := fun k v =>
    GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  have hPS : ParSurj D := GlobalTheory.T.pointParameterIsTypeParameter_of_tame D hPar h0 h5 hSplit hDep hDZ
  let P : PairedCharacterCondition.Pend D := mk lz hlz hSer hZeta Ω hΩ hChar Z hZL hPr hPS
  exact ⟨P, GlobalTheory.T.depthZeroAdmissible_all_pending_data D P hAdm, GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections D P hSec hCT⟩

end GlobalTheory.PendClose
