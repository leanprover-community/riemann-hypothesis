module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaApplyDScale
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaDegreeMapDomain
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GainOfCapacityLoss
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmRestNormOfPlace
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpV
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpVOf

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem ea_restSU (hG : RestGc p) : ea_RestSU X Y :=
  ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))

theorem first_theorem_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj =>
    ea_A1U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem second_lemma_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj =>
    ea_A2U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem hecke_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : RestBU X Y D :=
  fun hA v j hj i hi =>
    ea_BU D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brScale X) (ea_brClass X) (ea_brNum X) hA v j hj i hi

end Formalism.MainNotions.FormalGroupSystem.Pf
