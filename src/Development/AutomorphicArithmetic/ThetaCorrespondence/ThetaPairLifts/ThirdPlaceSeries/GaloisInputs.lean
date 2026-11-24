module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsToricEltOfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricPropertiesAllOfBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Adm2OfIsTriple
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfIsTriple
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetHypOfIsTripleOfGalHodge
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwGalInputs
theorem galois_inputs_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), _root_.UpperTheory.GalS.GalHodgeN D G.wd → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) ∧ BlochKatoReduction.adm2 D ∧ BlochKatoReduction.adm8 D ∧ AllGood D.nexp ∧ D.nexp.sig_all ∧ (∃ N0, BlochKatoReduction.adm9 D N0) ∧ BlochKatoReduction.adm10 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i := by
  intro hC hArt hTor D G hGH
  have h2 : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.adm2_of_isTriple_wildOne D G.triple (GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D G.wd G.lab)
  have hF : GlobalTheory.TypeLeaf.FrobDense D :=
    GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)
  have hg := _root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple G.chr hF hGH h2 G.triple
  have hs := _root_.GlobalTheory.Triple.adm8_allGood_sig_of_isTriple D G.triple
  have hL := GlobalTheory.LamTie.isToricElt_of_isLamTie D _ D.ntw G.lam G.lamOk G.lamTie
  obtain ⟨N0, h9, h10, -⟩ := GlobalTheory.ToricAssembly.toric_properties hArt hTor D hL.1
  exact ⟨hg.1, h2, hg.2.1, hs.2.1, hs.2.2, ⟨N0, h9⟩, h10,
    _root_.GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_nonzeroIndexPlace hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩
end GlobalTheory.TwGalInputs
end
