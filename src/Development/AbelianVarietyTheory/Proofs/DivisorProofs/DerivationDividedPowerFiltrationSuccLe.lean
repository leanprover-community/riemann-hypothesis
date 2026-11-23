module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.Derivation.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DerFil

theorem fil_succ_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) :
    fil δ (N + 1) ≤ fil δ N :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem prod_mem_fil {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ)
    (l : List (ℕ × B)) (hl : ∀ p ∈ l, p.2 ∈ J) (hN : N ≤ (l.map Prod.fst).sum) :
    (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ fil δ N :=
  Ideal.subset_span ⟨l, hl, hN, rfl⟩

theorem smul_deriv_prod_mem {R B M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J)
    (D : Derivation R B M) (N₀ : Submodule B M)
    (hD : ∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) (N : ℕ) :
    ∀ (l : List (ℕ × B)), (∀ p ∈ l, p.2 ∈ J) → ∀ (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) →
      N + 1 ≤ (l'.map Prod.fst).sum + (l.map Prod.fst).sum →
      (l'.map fun p ↦ δ.dpow p.1 p.2).prod • D ((l.map fun p ↦ δ.dpow p.1 p.2).prod) ∈
        fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro l
  induction l with
  | nil => intro _ l' _ _; simp
  | cons p l ih =>
    intro hl l' hl' hs
    have hp : p.2 ∈ J := hl p (by simp)
    have hl2 : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hs ⊢
    rw [Derivation.leibniz, smul_add, smul_smul, smul_smul]
    refine add_mem ?_ ?_
    · have hl3 : ∀ q ∈ p :: l', q.2 ∈ J := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hl' q hq
      have := ih hl2 (p :: l') hl3 (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa only [List.map_cons, List.prod_cons, mul_comm] using this
    · rcases p with ⟨k, x⟩
      cases k with
      | zero => simp [δ.dpow_zero hp]
      | succ m =>
        have h := hD m x hp
        set c := (l'.map fun p ↦ δ.dpow p.1 p.2).prod * (l.map fun p ↦ δ.dpow p.1 p.2).prod
        have e : c • D (δ.dpow (m + 1) x) =
            c • (D (δ.dpow (m + 1) x) - δ.dpow m x • D x) + (c * δ.dpow m x) • D x := by
          rw [smul_sub, smul_smul, sub_add_cancel]
        rw [e]
        refine add_mem (Submodule.mem_sup_right (N₀.smul_mem _ h)) (Submodule.mem_sup_left ?_)
        refine Submodule.smul_mem_smul ?_ Submodule.mem_top
        have hm := prod_mem_fil δ N (l' ++ (m, x) :: l)
          (by
            intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · exact hl' q hq
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact hp
              · exact hl2 q hq)
          (by simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hs ⊢; omega)
        simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hm
        convert hm using 1
        simp only [c]; ring

end GlobalTheory.DerFil


open GlobalTheory.DerFil in
theorem GlobalTheory.DerFil.deriv_fil_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M)
    (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) →
    ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  intro R B M _ _ _ _ _ _ _ J δ D N₀ hD N x hx
  induction hx using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨l, hl, hs, rfl⟩ := hb
    simpa using smul_deriv_prod_mem J δ D N₀ hD N l hl [] (by simp) (by simpa using hs)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x hx ih =>
    rw [smul_eq_mul, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ ih)
      (Submodule.mem_sup_left (Submodule.smul_mem_smul (fil_succ_le δ N hx) Submodule.mem_top))
