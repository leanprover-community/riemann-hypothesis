module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliWhittakerZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Expand
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Tensor

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

universe u v

theorem capelliCentral : CapelliCentralStatement.{u} := by
  intro 𝒰 _ _ n E x hE a b
  exact capelliC_central E hE x a b

theorem capelliExpand : CapelliExpandStatement.{u} := by
  intro 𝒰 _ _ m E om hE
  exact ⟨fun b c => capelli_expand_plus E hE om b c, fun a c => capelli_expand_minus E hE om a c⟩

theorem capelliTensor : CapelliTensorStatement.{u} := by
  intro M _ _ n E hE
  exact ⟨isGlRep_tensV E hE, isGlRep_tensVd E hE, casimir_tensV E, casimir_tensVd E⟩

theorem capelliAPlus : CapelliAPlusStatement.{u} := by
  intro M _ _ m E y om v hE hv
  exact eeV_nnPlus E hE y om v hv

theorem capelliAMinus : CapelliAMinusStatement.{u} := by
  intro M _ _ m E β om v hE hv
  exact eeVd_nnMinus E hE β om v hv

theorem capelliB : CapelliBStatement.{u, v} := by
  intro M R _ _ _ _ k r E D ψ l x hE hr hl hψ hD
  exact capelli_whittaker k r E D ψ l x hE hr hl hψ hD

theorem whittakerZeroStatement : WhittakerZeroStatement.{u, v} := by
  intro M R _ _ _ _ k E D l x hD
  exact capelli_whittaker_zero k E D l x hD

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
