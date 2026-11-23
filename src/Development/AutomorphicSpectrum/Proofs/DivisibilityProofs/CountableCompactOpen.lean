module

import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.Ar.RT.Inj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  apply GlobalTheory.ThK.Dbl.Prs.countable_compactOpen <;> assumption

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  apply GlobalTheory.ThK.Dbl.Prs.mem_span_indicator <;> assumption

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

end GlobalTheory.CompanionTheory.Ar.RT.Inj.Rank
end
