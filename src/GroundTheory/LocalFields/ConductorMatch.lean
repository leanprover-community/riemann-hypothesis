module

public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.Existence
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

@[expose] public section

noncomputable section

open ValuativeRel

namespace GroundTheory.LocalField

section Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]

def conductor : ℕ :=
  sInf {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}

theorem conductor_le_iff [IsSepClosure K Ω] (n : ℕ) :
    conductor L ≤ n ↔ unitFiltrationUnits K n ≤ (normUnits K L).range := by
  have hne : {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}.Nonempty :=
    exists_unitFiltrationUnits_le (isOpen_range_normUnits_and_finiteIndex L).1
  constructor
  · intro h
    exact (unitFiltrationUnits_antitone h).trans (Nat.sInf_mem hne)
  · intro h
    exact Nat.sInf_le h

end Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

section Conductor

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem unitFiltrationUnits_le_range_normUnits_iff (n : ℕ) :
    unitFiltrationUnits K n ≤ (normUnits K L).range ↔ upperRamificationGroup K L n = ⊥ := by
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L n, Subgroup.map_eq_bot_iff,
    ker_restrictAb_localArtinMap]

theorem upperRamificationGroup_natCast_eq_bot_iff (n : ℕ) :
    upperRamificationGroup K L n = ⊥ ↔ conductor L ≤ n := by
  rw [conductor_le_iff, unitFiltrationUnits_le_range_normUnits_iff]

end Conductor

section Ab


end Ab

end GroundTheory.LocalField
