module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedStepsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeilStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRowStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
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

namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowMainEqP := by
  intro h hB hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _h8, h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  refine GlobalTheory.T.equalWordGenericBound_of_normalisedSteps h1 h2 GlobalTheory.T.normalCount_genericRow h3 h4 h5 hB h6 h7 (h9 (GlobalTheory.T.genericFamilyStep_of_siegelWeil (GlobalTheory.St.swxs_of_siegelWeil h))) ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩

end GlobalTheory
