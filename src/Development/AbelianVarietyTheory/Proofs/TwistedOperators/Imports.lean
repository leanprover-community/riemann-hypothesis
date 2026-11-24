module

public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.SmulMemOfMemSpan

theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
