module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.psi_p_neighborhood_in_level_subgroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r₂ : Gr G 1), letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C); ∃ O : Set ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, r₂⁻¹ * psiP G z * r₂ ∈ KHT p G.m G.n 1 G.Fw := by
  first | (exact @GlobalTheory.TorCls.OpenP.openp) | (exact GlobalTheory.TorCls.OpenP.openp) | (intros; apply GlobalTheory.TorCls.OpenP.openp  <;> assumption)
