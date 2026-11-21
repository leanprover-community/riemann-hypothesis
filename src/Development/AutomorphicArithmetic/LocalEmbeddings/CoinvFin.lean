import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

open GlobalTheory.PRep Topology Filter

namespace UpperTheory.Dv.CoinvFin

section Alg

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

def orb (ρ : Representation ℂ G V) (v : V) : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => ρ g v)

theorem orb_stable (ρ : Representation ℂ G V) (v : V) : ∀ g, ∀ w ∈ orb ρ v, ρ g w ∈ orb ρ v := by
  intro g w hw
  refine (Submodule.span_le (p := (orb ρ v).comap (ρ g))).2 ?_ hw
  rintro _ ⟨x, rfl⟩
  exact Submodule.subset_span ⟨g * x, by simp⟩

theorem mem_fixed {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k.1 k.2⟩

def av (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] (v : V) : V :=
  ∑ q : K ⧸ K'.subgroupOf K, ρ (q.out : K) v

theorem av_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : K' ≤ stab ρ v) : ∀ k ∈ K, ρ k (av ρ K K' v) = av ρ K K' v := by
  intro k hk
  unfold av
  rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have h1 : ((((⟨k, hk⟩ : K) • q).out : K) : K ⧸ K'.subgroupOf K) = ((⟨k, hk⟩ * q.out : K) : K ⧸ K'.subgroupOf K) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
  have h2 : ρ _ v = v := hv (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1))
  rw [MulAction.toPerm_apply]
  conv_rhs => rw [← h2]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem av_of_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) : av ρ K K' v = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) • v := by
  unfold av
  rw [Finset.sum_congr rfl fun q _ => hv _ (q.out).2, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

end Alg

section Top

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem finite_quot {K K' : Subgroup G} (c : IsCompact (K : Set G)) (o : IsOpen (K' : Set G)) :
    Finite (K ⧸ K'.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 c
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K K' o)

theorem mem_of_span (ρ : Representation ℂ G V) {K : Subgroup G} (c : IsCompact (K : Set G)) (S : Set V) (W₀ : Submodule ℂ V)
    (hS : ∀ s ∈ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' s ∈ W₀)
    {w : V} (hw : w ∈ Submodule.span ℂ S) (hfix : ∀ k ∈ K, ρ k w = w) : w ∈ W₀ := by
  have key : ∀ w ∈ Submodule.span ℂ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧
      ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' w ∈ W₀ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => exact ⟨⊤, isOpen_univ, fun K' _ _ => by simp [av]⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      obtain ⟨K₂, o₂, h₂⟩ := hy
      refine ⟨K₁ ⊓ K₂, o₁.inter o₂, fun K' h _ => ?_⟩
      have := add_mem (h₁ K' (h.trans inf_le_left)) (h₂ K' (h.trans inf_le_right))
      simpa [av, Finset.sum_add_distrib] using this
    | smul a x _ hx =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      refine ⟨K₁, o₁, fun K' h _ => ?_⟩
      have := W₀.smul_mem a (h₁ K' h)
      simpa [av, Finset.smul_sum] using this
  obtain ⟨K₀, o, h⟩ := key w hw
  haveI := finite_quot c o
  letI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  have h1 := h K₀ le_rfl
  rw [av_of_fixed ρ K K₀ hfix] at h1
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1



end Top

theorem exists_finiteDimensional {G₁ G₂ V S X J : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup X] [Module ℂ X] [Finite J]
    (π : Representation ℂ G₂ V) (ω₁ : Representation ℂ G₁ S) (ω₂ : Representation ℂ G₂ S) (ζ : Representation ℂ G₁ X)
    (b : V →ₗ[ℂ] S →ₗ⋆[ℂ] X) (D : J → Submodule ℂ S) (hπ : IsAdmissible π)
    (hD : ∀ j g, ∀ Ψ ∈ D j, ω₁ g Ψ ∈ D j) (eq1 : ∀ g u Ψ, ζ g (b u Ψ) = b u (ω₁ g Ψ))
    (eq2 : ∀ h u Ψ, b (π h u) (ω₂ h Ψ) = b u Ψ)
    (sm1 : ∀ j, ∀ Ψ ∈ D j, IsOpen (stab ω₁ Ψ : Set G₁)) (sm2 : ∀ j, ∀ Ψ ∈ D j, IsOpen (stab ω₂ Ψ : Set G₂))
    (K₂ : Subgroup G₂) (o₂ : IsOpen (K₂ : Set G₂)) (c₂ : IsCompact (K₂ : Set G₂)) (K : Subgroup G₁) (c : IsCompact (K : Set G₁))
    (hgen : ∀ j, ∃ A : Set S, A.Finite ∧ (∀ a ∈ A, a ∈ D j) ∧
      ∀ Ψ ∈ D j, (∀ k ∈ K, ω₁ k Ψ = Ψ) → Ψ ∈ Submodule.span ℂ {x | ∃ a ∈ A, ∃ h, x = ω₂ h a}) :
    ∃ W₀ : Submodule ℂ X, FiniteDimensional ℂ W₀ ∧
      ∀ φ ∈ Submodule.span ℂ {y | ∃ j u, ∃ Ψ ∈ D j, y = b u Ψ}, (∀ k ∈ K, ζ k φ = φ) → φ ∈ W₀ := by
  choose A hAf hAD hA using hgen
  haveI : ∀ j, Finite (A j) := fun j => hAf j
  have hc : ∀ j (a : A j), IsCompact ((K₂ ⊓ stab ω₂ a.1 : Subgroup G₂) : Set G₂) := fun j a =>
    c₂.inter_right ((stab ω₂ a.1).isClosed_of_isOpen (sm2 j _ (hAD j _ a.2)))
  haveI : ∀ j (a : A j), FiniteDimensional ℂ (fixed π (K₂ ⊓ stab ω₂ a.1)) := fun j a =>
    hπ.2 _ (o₂.inter (sm2 j _ (hAD j _ a.2))) (hc j a)
  let W₀ : Submodule ℂ X := ⨆ j, ⨆ a : A j, (fixed π (K₂ ⊓ stab ω₂ a.1)).map (b.flip a.1)
  have h1 : ∀ j (a : A j) u, b u a.1 ∈ W₀ := by
    intro j a u
    haveI := finite_quot (K' := stab π u) (hc j a) (hπ.1 u)
    letI := Fintype.ofFinite ((K₂ ⊓ stab ω₂ a.1 : Subgroup G₂) ⧸ (stab π u).subgroupOf (K₂ ⊓ stab ω₂ a.1))
    have h2 : b (av π (K₂ ⊓ stab ω₂ a.1) (stab π u) u) a.1 ∈ W₀ :=
      Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem a ⟨_, mem_fixed.2 (av_fixed π _ _ le_rfl), rfl⟩)
    have h3 : ∀ k ∈ K₂ ⊓ stab ω₂ a.1, b (π k u) a.1 = b u a.1 := fun k hk => by
      rw [← eq2 k u, show ω₂ k a.1 = a.1 from hk.2]
    rw [av, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun q _ => h3 _ (q.out).2, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, Finset.card_univ] at h2
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h2
  refine ⟨W₀, inferInstance, fun φ hφ hfix => mem_of_span ζ c _ W₀ ?_ hφ hfix⟩
  rintro _ ⟨j, u, Ψ, hΨ, rfl⟩
  refine ⟨stab ω₁ Ψ, sm1 j Ψ hΨ, fun K' h _ => ?_⟩
  have h4 : av ζ K K' (b u Ψ) = b u (av ω₁ K K' Ψ) := by simp only [av, eq1, map_sum]
  rw [h4]
  refine (Submodule.span_le (p := W₀.comap (b u))).2 ?_
    (hA j _ (Submodule.sum_mem _ fun q _ => hD j _ _ hΨ) (av_fixed ω₁ K K' h))
  rintro _ ⟨a, ha, g, rfl⟩
  have h5 := eq2 g (π g⁻¹ u) a
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h5
  show b u (ω₂ g a) ∈ W₀
  rw [h5]
  exact h1 j ⟨a, ha⟩ _

end UpperTheory.Dv.CoinvFin

end
