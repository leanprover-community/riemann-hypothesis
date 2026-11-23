module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaHStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeavesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SnFam

namespace GlobalTheory.SnFamTop

theorem stepFamG_of_SWXS (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.Pf.MainEqFam.StepFamG :=
  GlobalTheory.T.genericRow_familyStep_of_leaves
    (fun D h => GlobalTheory.localMass_le_genericMass_nine _ _ h)
    GlobalTheory.T.differentLocalIdentity_familiesLemmaH GlobalTheory.T.genericScalarClassTerms_formFamily GlobalTheory.T.familyRowWeightSumUnfoldingIdentity (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW) GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof GlobalTheory.T.familyLocalObjectsExistAtTerms_proof

end GlobalTheory.SnFamTop
