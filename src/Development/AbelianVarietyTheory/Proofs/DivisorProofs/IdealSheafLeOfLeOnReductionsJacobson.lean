import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedEmptyOfUniversallyClosedOfLeJacobson
import BuildAid.ForwardExisting

section
section
namespace GlobalTheory

theorem krull_inter_ideal_local (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add, hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  atlas_forward_decl GlobalTheory.krull_inter_ideal_local
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem ideal_le_on_basicOpen {X : Scheme.{0}} (a a' : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U)) (h : ∀ s ∈ a.ideal U, g * s ∈ a'.ideal U) :
    a.ideal (X.affineBasicOpen g) ≤ a'.ideal (X.affineBasicOpen g) := by
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  have key : (a.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ≤
      (a'.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
    rw [Ideal.mem_comap]
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (h s hs)
  rw [← a.map_ideal_basicOpen, ← a'.map_ideal_basicOpen]
  exact key

theorem exists_affineOpen_mem {X : Scheme.{0}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 :=
  TopologicalSpace.Opens.mem_iSup.1 ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))

theorem le_of_le_reductions : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R))
    (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) →
    (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  intro R _ I hI V _ p a a' hUC hle
  let S := {U : V.affineOpens // a.ideal U ≤ a'.ideal U}
  have h1 : ∀ x : V, x ∉ a'.support → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff] at hx
    push_neg at hx
    obtain ⟨f, hf, hxf⟩ := hx
    exact ⟨⟨V.affineBasicOpen f, ideal_le_on_basicOpen a a' U f fun s _ => Ideal.mul_mem_right _ _ hf⟩, hxf⟩
  have h2 : ∀ x : V, I ≤ (p x).asIdeal → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    haveI : IsNoetherianRing Γ(V, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.krull_intersection_ideal_local_form Γ(V, U) (I.map (cst p U.1)) (a.ideal U) (a'.ideal U)
      (fun e => by
        have := hle e U
        rwa [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, Ideal.map_pow] at this)
    refine ⟨⟨V.affineBasicOpen (1 - r), ideal_le_on_basicOpen a a' U _ hr'⟩, ?_⟩
    have hsupp : x ∈ (baseIdeal p I).support := (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R V p I x).2 hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, baseIdeal_ideal, Scheme.mem_zeroLocus_iff]
      at hsupp
    have hxr := hsupp r hr
    show x ∈ V.basicOpen (1 - r)
    rw [Scheme.mem_basicOpen _ _ _ hU] at hxr ⊢
    rw [map_sub, map_one]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hxr
  let O : V.Opens := ⨆ U : S, U.1.1
  have hZ := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI a'.subscheme (a'.subschemeι ≫ p) hUC
    (a'.subschemeι ⁻¹' (O : Set V)ᶜ) (O.isOpen.isClosed_compl.preimage a'.subschemeι.continuous)
    (fun z hz hIz => hz (by
      obtain ⟨U, hU⟩ := h2 (a'.subschemeι z) (by simpa using hIz)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩))
  have hO : O = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxO
    by_cases hx : x ∈ a'.support
    · have hx' : x ∈ Set.range a'.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      have : z ∈ (∅ : Set a'.subscheme) := hZ ▸ hxO
      exact this
    · obtain ⟨U, hU⟩ := h1 x hx
      exact hxO (TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩)
  exact Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) hO (fun U => U.2)

end GlobalTheory.FormalAlg
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R)) (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) → (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  atlas_forward_decl GlobalTheory.FormalAlg.le_of_le_reductions
end
