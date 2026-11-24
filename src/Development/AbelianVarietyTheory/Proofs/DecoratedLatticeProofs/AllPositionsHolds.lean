module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPositionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainOneIndexAtOfClassSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainSupportAtOfPatternStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchangeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem allPositions_holds : AllPositions := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hsupp : S.SupportAt t := GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern k s κ S t hpat
  have hclass : S.ClassAt t ν := GlobalTheory.T.symmetricLevelChain_classAt_every_position k ν hν s κ S t
  exact ⟨GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricLevelChain_unfolded_position_exchange k ν hν s κ S t hpat⟩

end GlobalTheory.SymChain
