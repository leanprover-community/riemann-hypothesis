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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.LocalizedModule.Int

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem mem_map_smul_top_iff {S R M : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M] (K : Ideal S) (m : M) :
    m ∈ (K.map (algebraMap S R) • ⊤ : Submodule R M) ↔ m ∈ (K • ⊤ : Submodule S M) := by
  have h := Submodule.restrictScalars_map_smul_eq K (⊤ : Submodule R M)
  rw [Submodule.restrictScalars_top] at h
  rw [← h, Submodule.restrictScalars_mem]

private theorem map_mem_smul_top {S M M' : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') (K : Ideal S) {m : M}
    (h : m ∈ (K • ⊤ : Submodule S M)) : f m ∈ (K • ⊤ : Submodule S M') := by
  have h2 : f m ∈ (K • ⊤ : Submodule S M).map f := Submodule.mem_map_of_mem h
  rw [Submodule.map_smul''] at h2
  exact Submodule.smul_mono (le_refl K) le_top h2

private theorem mem_of_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) (t : T) {x : M'}
    (h : (t : S) • x ∈ (K • ⊤ : Submodule S M')) : x ∈ (K • ⊤ : Submodule S M') := by
  have hu := IsLocalizedModule.map_units f t
  have e := LinearMap.congr_fun hu.unit.inv_mul x
  rw [Module.End.mul_apply, IsUnit.unit_spec, Module.End.one_apply, Module.algebraMap_end_apply] at e
  rw [← e]
  exact map_mem_smul_top _ K h

private theorem exists_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) {m : M}
    (h : f m ∈ (K • ⊤ : Submodule S M')) : ∃ t : T, (t : S) • m ∈ (K • ⊤ : Submodule S M) := by
  have key : ∀ x ∈ (K • ⊤ : Submodule S M'), ∃ (s : T) (m' : M),
      m' ∈ (K • ⊤ : Submodule S M) ∧ (s : S) • x = f m' := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro k hk x _
      obtain ⟨⟨m0, s⟩, hs⟩ := IsLocalizedModule.surj T f x
      simp only at hs
      refine ⟨s, k • m0, Submodule.smul_mem_smul hk Submodule.mem_top, ?_⟩
      rw [map_smul, ← hs, Submonoid.smul_def, smul_comm]
    · intro x y hx hy
      obtain ⟨s1, m1, hm1, h1⟩ := hx
      obtain ⟨s2, m2, hm2, h2⟩ := hy
      refine ⟨s1 * s2, (s2 : S) • m1 + (s1 : S) • m2,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hm1) (Submodule.smul_mem _ _ hm2), ?_⟩
      rw [map_add (f := _), map_smul, map_smul, ← h1, ← h2, smul_add, Submonoid.coe_mul, mul_smul, mul_smul,
        smul_comm (s1 : S) (s2 : S) x]
  obtain ⟨s, m', hm', he⟩ := key _ h
  rw [← map_smul] at he
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) he
  refine ⟨c * s, ?_⟩
  simp only [Submonoid.smul_def] at hc
  rw [Submonoid.coe_mul, mul_smul, hc]
  exact Submodule.smul_mem _ _ hm'

theorem UpperTheory.V.AlgebraTools.qRegAt_map :
    ∀ (S R σ : Type) [CommRing S] [CommRing R] [Algebra S R] [Finite σ] (y : σ → S) (J : Ideal S) (a : ℕ),
      (∀ (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M],
        QRegAt M y J a ↔ QRegAt M (fun s => algebraMap S R (y s)) (J.map (algebraMap S R)) a) ∧
      (∀ (T : Submonoid S) (M : Type) [AddCommGroup M] [Module S M] (M' : Type) [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f], QRegAt M y J a → QRegAt M' y J a) := by
  intro S R σ _ _ _ _ y J a
  constructor
  · intro M _ _ _ _
    have hv : ∀ α, GlobalTheory.monoVal (fun s => algebraMap S R (y s)) α = algebraMap S R (GlobalTheory.monoVal y α) :=
      fun α => (GlobalTheory.map_monoVal _ _ _).symm
    have e1 : Ideal.span (Set.range fun s => algebraMap S R (y s)) =
        (Ideal.span (Set.range y)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    unfold QRegAt
    simp only [hv, algebraMap_smul, e1, ← Ideal.map_pow, ← Ideal.map_sup, mem_map_smul_top_iff]
  · intro T M _ _ M' _ _ f _ hM
    unfold QRegAt at hM ⊢
    intro c' hc' α
    obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite T f c'
    have hs' : ∀ i, ∃ m, f m = (s : S) • c' i := fun i => LinearMap.mem_range.1 (hs i)
    choose c hc using hs'
    have h1 : f (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) ∈
        ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule S M') := by

      simp only [map_sum, map_smul, hc]
      have e : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((s : S) • c' β)) =
          (s : S) • ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c' β := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun β _ => smul_comm _ _ _
      rw [e]
      exact Submodule.smul_mem _ _ hc'
    obtain ⟨t, ht⟩ := exists_smul_mem T f _ h1
    rw [Finset.smul_sum] at ht
    have h2 := hM (fun β => (t : S) • c β) (by
      rw [show (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((t : S) • c β)) =
          ∑ β : GlobalTheory.MonoDeg σ a, (t : S) • (GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) from
        Finset.sum_congr rfl fun β _ => smul_comm _ _ _]
      exact ht)
    have h3 := map_mem_smul_top f _ (h2 α)
    rw [map_smul, hc, smul_smul] at h3
    exact mem_of_smul_mem T f _ (t * s) (by rwa [Submonoid.coe_mul])
