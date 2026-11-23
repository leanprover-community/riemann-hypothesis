module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
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

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.isQuasiRegularSeq_of_tower :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (y : σ → R) (M : Type) [AddCommGroup M] [Module R M] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (q : ∀ k, M →ₗ[R] P k),
      (∀ k, Function.Surjective (q k)) → (∀ k, LinearMap.ker (q k) = Ideal.span (Set.range y) ^ k • ⊤) →
      (∀ a k, a < k → QRegAt (P k) y ⊥ a) → GlobalTheory.IsQuasiRegularSeq M y := by
  intro R σ _ _ y M _ _ P _ _ q hs hk hq
  rw [isQuasiRegularSeq_iff_qRegAt]
  intro a c hc α
  simp only [sup_bot_eq] at hc ⊢
  have h := hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by

    rw [← hk, LinearMap.mem_ker, map_sum] at hc
    simp only [map_smul] at hc
    rw [hc]
    exact zero_mem _) α
  simp only [sup_bot_eq] at h
  have htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]
  rw [htop, ← Submodule.map_smul''] at h
  have h2 : c α ∈ Submodule.comap (q (a + 1))
      (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M)) := h
  rw [Submodule.comap_map_eq, hk] at h2
  have hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))
  rwa [sup_eq_left.2 hle] at h2
