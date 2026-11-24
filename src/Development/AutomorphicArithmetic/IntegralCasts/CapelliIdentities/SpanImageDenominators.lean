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

theorem UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image :
    ∀ {A F M N : Type} [inst : CommRing A]
    [IsDomain A] [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup M]
    [inst_6 : _root_.Module A M] [inst_7 : AddCommGroup N] [inst_8 : _root_.Module A N] [inst_9 : _root_.Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M),
    ∀ y ∈ Submodule.span F ((⇑φ : M → N) '' T),
      ∃ (d : A), d ≠ (0 : A) ∧ ∃ w ∈ Submodule.span A T, d • y = (φ : M → N) w := by
  intro A F M N _ _ _ _ _ _ _ _ _ _ _ φ T y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨1, one_ne_zero, m, Submodule.subset_span hm, one_smul _ _⟩
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul c x _ hx =>
    obtain ⟨d, hd, w, hw, e⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hd, a • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    have hab' : c * algebraMap A F b = algebraMap A F a := hab
    rw [map_smul, ← e, ← algebraMap_smul F ((b : A) * d), ← algebraMap_smul F a,
      ← algebraMap_smul F d, smul_smul, smul_smul, ← hab', map_mul]
    congr 1
    ring
