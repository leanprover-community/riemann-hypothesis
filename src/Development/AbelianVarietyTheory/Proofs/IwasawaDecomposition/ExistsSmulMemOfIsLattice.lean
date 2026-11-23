module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.SmulMemOfIsLattice

theorem exists_smul_mem_of_isLattice {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (B : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n))
    (hB : Submodule.IsFullLattice E B) (x : Formalism.L2.Col.Sp E n) :
    ∃ r ∈ nonZeroDivisors (NumberField.RingOfIntegers E), r • x ∈ B := by
  have hx : x ∈ Submodule.span E (B : Set (Formalism.L2.Col.Sp E n)) := by
    rw [hB.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_mem hr hs, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ hry
    · rw [mul_smul]; exact B.smul_mem _ hsz
  | smul c y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    refine ⟨r * b, mul_mem hr hb, ?_⟩
    have hb0 : algebraMap (NumberField.RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h : (r * b) • ((algebraMap (NumberField.RingOfIntegers E) E a / algebraMap (NumberField.RingOfIntegers E) E b) • y) = a • (r • y) := by
      rw [← algebraMap_smul E (r * b), ← algebraMap_smul E a, ← algebraMap_smul E r y, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h]
    exact B.smul_mem _ hry

end GlobalTheory.SmulMemOfIsLattice
