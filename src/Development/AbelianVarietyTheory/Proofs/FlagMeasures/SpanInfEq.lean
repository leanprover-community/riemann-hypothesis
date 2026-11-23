module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.SpanInfEq

open NumberField

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h

theorem span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T :=
  fun L hL T => span_inf_eq L hL T

end GlobalTheory.SpanInfEq
