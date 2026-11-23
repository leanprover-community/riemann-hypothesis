module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecPrOfZSpecTypeTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspacesStatement
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower D M AV i (CS i)) (TC i) II PZ
      (GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := GlobalTheory.T.typeSpace_projection_to_pointEigenspaces D M i HT HR AV SU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
