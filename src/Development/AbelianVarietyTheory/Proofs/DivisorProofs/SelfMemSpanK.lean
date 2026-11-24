module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def spanK (φ : Sm E a) : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)

theorem spanK_stable (φ : Sm E a) : ∀ k, ∀ w ∈ spanK E a φ, cptRep E a k w ∈ spanK E a φ := by
  intro k w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    exact Submodule.subset_span ⟨k * k', by simp only [map_mul, mul_apply_eq_comp]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem self_mem_spanK (φ : Sm E a) : φ ∈ spanK E a φ :=
  Submodule.subset_span ⟨1, by simp only [map_one, one_apply_eq_self]⟩

def mapsJ (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) where
  carrier := {T | T ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T w) = 0}
  zero_mem' := ⟨zero_mem _, fun z _ _ w => by simp⟩
  add_mem' {T T'} h h' := ⟨add_mem h.1 h'.1, fun z hz h0 w => by
    simp [h.2 z hz h0 w, h'.2 z hz h0 w]⟩
  smul_mem' c T h := ⟨Submodule.smul_mem _ c h.1, fun z hz h0 w => by simp [h.2 z hz h0 w]⟩

end GlobalTheory.AutGrowth
