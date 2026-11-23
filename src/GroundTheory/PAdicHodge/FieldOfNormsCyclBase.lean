module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import GroundTheory.LocalFields.Examples
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace CyclNorms

open GroundTheory.LocalField ValuativeRel

variable (p : ℕ) [Fact p.Prime]

scoped instance padicAlgCl_valuativeRel : ValuativeRel (PadicAlgCl p) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := PadicAlgCl p))

variable {p}

theorem vle_iff_norm_le (x y : PadicAlgCl p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

scoped instance padicAlgCl_compatible : (NormedField.valuation (K := PadicAlgCl p)).Compatible :=
  Valuation.Compatible.ofValuation _

scoped instance padicAlgCl_isValuativeTopology : IsValuativeTopology (PadicAlgCl p) := by
  let : Valued (PadicAlgCl p) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (PadicAlgCl p) NNReal).Compatible := padicAlgCl_compatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

scoped instance padicAlgCl_valuativeExtension : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun {a b} ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

end CyclNorms

end GroundTheory.PAdicHodge
