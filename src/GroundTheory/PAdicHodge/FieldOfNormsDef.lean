module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Norm.Defs
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.LocalFields.FormalGroups.Truncation
public import GroundTheory.PAdicHodge.FieldOfNormsAPF
public import GroundTheory.PAdicHodge.FieldOfNormsTower

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

section Def

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {L : IntermediateField K Ω}

variable (K Ω L) in
abbrev FinSub : Type _ := {E : IntermediateField K Ω // E ≤ L ∧ FiniteDimensional K E}

abbrev inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') : Algebra E E' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra


open Classical in
def relNorm {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : Ω :=
  if hy : y ∈ E' then ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) else 0


variable (K Ω L) in
def FieldOfNorms : Type _ :=
  {x : FinSub K Ω L → Ω //
    (∀ E, x E ∈ E.1) ∧ ∀ E E' : FinSub K Ω L, ∀ h : E.1 ≤ E'.1, relNorm h (x E') = x E}

end Def


variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p) (L : IntermediateField K Ω)

variable {t L}



end NormTower



variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]



variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]

namespace APFData

variable (d : APFData L)

end APFData


end GroundTheory.PAdicHodge
