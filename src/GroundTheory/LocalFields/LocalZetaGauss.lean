module

public import GroundTheory.LocalFields.LocalZetaChar
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Quotient


variable (K) in
abbrev unitsModFiltration (c : ℕ) : Type _ :=
  unitFiltrationUnits K 0 ⧸ (unitFiltrationUnits K c).subgroupOf (unitFiltrationUnits K 0)

instance finite_unitsModFiltration (c : ℕ) : Finite (unitsModFiltration K c) := by
  have : CompactSpace (unitFiltrationUnits K 0) :=
    isCompact_iff_compactSpace.mp isCompact_unitFiltrationUnits_zero
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact (isOpen_unitFiltrationUnits c).preimage continuous_subtype_val

noncomputable instance fintype_unitsModFiltration (c : ℕ) : Fintype (unitsModFiltration K c) :=
  Fintype.ofFinite _

def unitsModRep {c : ℕ} (t : unitsModFiltration K c) : Kˣ :=
  ((Quotient.out t : unitFiltrationUnits K 0) : Kˣ)

def unitsModCoset {c : ℕ} (t : unitsModFiltration K c) : Set Kˣ :=
  (fun x => (unitsModRep t)⁻¹ * x) ⁻¹' (unitFiltrationUnits K c : Set Kˣ)

end Quotient

variable [MeasurableSpace K] [BorelSpace K]

section Integral

end Integral

section Gauss

variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}


variable (χ ψ) in
def gaussSum : ℂ :=
  ∑ t : unitsModFiltration K (quasiCharConductor χ),
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t) : ℂˣ) : ℂ)⁻¹ *
      (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t : Kˣ) : K) : ℂ)

end Gauss

end GroundTheory.LocalField
