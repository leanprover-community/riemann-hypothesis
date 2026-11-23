module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.NatMultipleIntegralSmulBound

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : RingOfIntegers E, (b : E) = (m : E) * a := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy),
    ⟨y • (y • a), (mem_integralClosure_iff ℤ E).2 (hint.smul y)⟩, ?_⟩
  show y • (y • a) = ((y.natAbs * y.natAbs : ℕ) : E) * a
  rw [smul_smul, zsmul_eq_mul, ← Int.cast_natCast, Int.natAbs_mul_self]

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  apply GlobalTheory.PrincLat.exists_nat_smul_mem <;> assumption

theorem exists_nat_smul_le {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx

end GlobalTheory.NatMultipleIntegralSmulBound
