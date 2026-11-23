module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.AinfPlusInjectivity.CoeffLMul
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

noncomputable section

namespace period_ring_base

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

theorem base_ainf_φ (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l :=
  BaseC.ainf_φ

theorem base_ainf_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l :=
  BaseC.ainf_σ

theorem base_ainf_plus (l : ℕ) [Fact l.Prime] : ∀ x ∈ Ainf' l, ι l x ∈ Plus l :=
  BaseC.ainf_plus

theorem base_ainf_eig (l : ℕ) [Fact l.Prime] :
    ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0 :=
  fun h m hm x hx he => BaseC.ainf_eig h m hm x hx he

end period_ring_base
