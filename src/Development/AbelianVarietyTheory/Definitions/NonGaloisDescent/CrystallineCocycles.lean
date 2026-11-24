module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.HyodoDef

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def geometricCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ b : V ⊗[Qp] BdR, ∀ g, c g ⊗ₜ[Qp] (1 : BdR) = actVdR PD ρ g b - b}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def crystallineCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
    ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, map_zero _, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hxφ, hx⟩ ⟨hb, y, hyφ, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, by rw [map_add (f := _), hxφ, hyφ], fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hxφ, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, by rw [map_smul, hxφ], fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

end GlobalTheory.HyodoDef

end
