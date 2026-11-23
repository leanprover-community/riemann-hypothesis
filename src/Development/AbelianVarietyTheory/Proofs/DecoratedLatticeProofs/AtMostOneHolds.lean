module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPatternStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClassStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPatternStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPatternStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem atMostOne_holds : AtMostOne := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S t
  have hclass : S.OneClass t ν := GlobalTheory.T.symmetricChain_oneLatticeClass k ν hν s κ S t
  have hsupp : S.SupportOne t := GlobalTheory.T.symmetricChain_supportOne_of_pattern k s κ S t hpat
  exact ⟨GlobalTheory.T.symData_oneIndex_of_oneClass_of_supportOne k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricChain_projected_level_of_pattern k s κ S t hpat, GlobalTheory.T.symmetricChain_oneCoupling_coset_of_pattern k s κ S t hpat⟩

end GlobalTheory.SymChain
