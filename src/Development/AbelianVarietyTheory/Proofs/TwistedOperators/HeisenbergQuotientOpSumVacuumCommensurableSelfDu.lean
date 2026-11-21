import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
import BuildAid.ForwardExisting

section
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

theorem vacuum_unique_of_selfDual {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (Λ : Submodule R X)
    (hΛ : SelfDual γ Λ) (s : M) (hs : s ≠ 0) (hfix : Fixes W Λ s)
    (hspan : Submodule.span ℂ (Set.range fun x => W x s) = ⊤) (v : M) (hv : Fixes W Λ v) : ∃ c : ℂ, v = c • s := by
  have key : ∀ z : X, W z s = (γ (w • (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) : X))
      (z - Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)))⁻¹ • W (Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ)) s := by
    intro z
    set t : X := Quotient.out (Submodule.Quotient.mk z : X ⧸ Λ) with ht
    have hmem : z - t ∈ Λ := by
      rw [← Submodule.Quotient.eq]
      exact (Quotient.out_eq (Submodule.Quotient.mk z : X ⧸ Λ)).symm
    have h1 := h.comp t (z - t) s
    rw [hfix _ hmem, add_sub_cancel] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]
  have hli : LinearIndependent ℂ (fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    refine linearIndependent_of_simultaneous_eigen _ (fun q (a : Λ) => γ a (Quotient.out q)) (fun a : Λ => W a) ?_ ?_ ?_
    · intro q q' hq
      have hm : (Quotient.out q : X) - Quotient.out q' ∈ Λ := by
        rw [hΛ]
        intro a ha
        apply h.swap_eq_one
        have h1 : γ a (Quotient.out q) = γ a (Quotient.out q') := congrFun hq ⟨a, ha⟩
        rw [sub_eq_add_neg, h.add_right, h.neg_right, h1, mul_inv_cancel₀ (h.ne_zero _ _)]
      rw [← Submodule.Quotient.eq] at hm
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      have e2 : (Submodule.Quotient.mk (Quotient.out q') : X ⧸ Λ) = q' := Quotient.out_eq q'
      rw [← e1, ← e2, hm]
    · intro a q
      rw [h.comm, hfix a a.2]
    · intro q h0
      have h1 := h.neg_comp (Quotient.out q) s
      rw [h0, map_zero] at h1
      exact hs ((smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _))
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun q : X ⧸ Λ => W (Quotient.out q) s) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    show W z s ∈ _
    rw [key z]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let b := Module.Basis.mk hli hsp
  have hb : ∀ q, b q = W (Quotient.out q) s := fun q => Module.Basis.mk_apply hli hsp q
  have hcoord : ∀ a ∈ Λ, ∀ q x, b.coord q (W a x) = γ a (Quotient.out q) * b.coord q x := by
    intro a ha q x
    have e : (b.coord q).comp (W a) = γ a (Quotient.out q) • b.coord q := by
      refine b.ext fun q' => ?_
      rw [LinearMap.comp_apply, hb, h.comm, hfix a ha, ← hb, LinearMap.smul_apply, map_smul, smul_eq_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hq
      · rw [hq]
      · simp
    exact LinearMap.congr_fun e x
  have h0 : (Quotient.out (0 : X ⧸ Λ) : X) ∈ Λ :=
    (Submodule.Quotient.mk_eq_zero Λ).1 (Quotient.out_eq (0 : X ⧸ Λ))
  have hb0 : b 0 = s := by rw [hb, hfix _ h0]
  have hvan : ∀ q : X ⧸ Λ, q ≠ 0 → b.repr v q = 0 := by
    intro q hq
    have hn : (Quotient.out q : X) ∉ Λ := fun hm => hq (by
      have e1 : (Submodule.Quotient.mk (Quotient.out q) : X ⧸ Λ) = q := Quotient.out_eq q
      rw [← e1]; exact (Submodule.Quotient.mk_eq_zero Λ).2 hm)
    rw [hΛ] at hn
    push_neg at hn
    obtain ⟨a, ha, hne⟩ := hn
    have hne' : γ a (Quotient.out q) ≠ 1 := fun e => hne (h.swap_eq_one e)
    have e := hcoord a ha q v
    rw [hv a ha, Module.Basis.coord_apply] at e
    have e2 : (γ a (Quotient.out q) - 1) * b.repr v q = 0 := by rw [sub_mul, ← e]; ring
    exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne')
  refine ⟨b.repr v 0, b.ext_elem fun q => ?_⟩
  rw [map_smul, ← hb0, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hq : (0 : X ⧸ Λ) = q
  · subst hq; simp
  · rw [if_neg hq, mul_zero, hvan q (Ne.symm hq)]

end GlobalTheory.SphTheta

end
end

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuum_unique_of_selfDual : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ v, Fixes W Λ v → ∃ c : ℂ, v = c • s := by
  atlas_forward_decl GlobalTheory.SphTheta.vacuum_unique_of_selfDual
end

section
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem sumOp_vec_zero {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) : sumOp W A B 0 = 0 := by
  unfold sumOp; simp

theorem form_translate_vacuum {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) {Λ : Submodule R X}
    (hΛ : SelfDual γ Λ) {s : M} (hs : Fixes W Λ s) (e : M →ₗ[ℂ] ℂ) (he : ∀ a ∈ Λ, ∀ v, e (W a v) = e v) (x : X) :
    e (W x s) = if x ∈ Λ then e s else 0 := by
  split_ifs with hx
  · rw [hs x hx]
  · obtain ⟨a, ha, hne⟩ : ∃ a ∈ Λ, γ x a ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hx ((hΛ x).2 hc)
    have h1 : e (W x s) = γ a x * e (W x s) := by
      conv_lhs => rw [← he a ha (W x s)]
      rw [h.comm a x s, hs a ha, map_smul, smul_eq_mul]
    have h2 : γ a x ≠ 1 := by
      rw [h.swap x a]
      intro h3
      exact hne (inv_eq_one.1 h3)
    have h3 : (1 - γ a x) * e (W x s) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm h2))

theorem sumOp_vacuum_lift : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  intro R X M _ _ _ _ _ σ w γ W h Λ hΛ s hs0 hs hspan Λ' hΛ' hidx
  obtain ⟨hidx', hss⟩ := sumOp_sumOp_eq_idx_smul h Λ Λ' hΛ hΛ' hidx
  obtain ⟨⟨n, f, hf, ht⟩, hfix, -⟩ := (sumOp_transversal h Λ Λ' hΛ').2.1 hidx
  have hs'fix : Fixes W Λ' (sumOp W Λ Λ' s) := hfix s hs
  have hback := hss s hs
  have hidxC : (idx Λ Λ' : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hne : sumOp W Λ Λ' s ≠ 0 := by
    intro h0
    rw [h0, sumOp_vec_zero] at hback
    exact hs0 ((smul_eq_zero.1 hback.symm).resolve_left hidxC)
  have hidx2 : idx Λ' Λ ≠ 0 := by rw [hidx']; exact hidx
  obtain ⟨⟨m, g, hg, hgt⟩, -, -⟩ := (sumOp_transversal h Λ' Λ hΛ).2.1 hidx2
  have hsum := ((sumOp_transversal h Λ' Λ hΛ).1 _ hs'fix (Fin m) g hg hgt).1
  have hsE : s = ((idx Λ Λ' : ℂ))⁻¹ • ∑ i, W (g i) (sumOp W Λ Λ' s) := by
    rw [← hsum, hback, smul_smul, inv_mul_cancel₀ hidxC, one_smul]
  have hmem : ∀ x, W x s ∈ Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) := by
    intro x
    rw [congrArg (W x) hsE, map_smul, map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [h.comp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hspan' : Submodule.span ℂ (Set.range fun y => W y (sumOp W Λ Λ' s)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmem x
  refine ⟨⟨hne, hs'fix, hspan'⟩, fun e he1 he v hv => ?_⟩
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergVacuum_unique_of_selfDual h Λ' hΛ' _ hne hs'fix hspan' v hv
  have hes' : e (sumOp W Λ Λ' s) = 1 := by
    rw [((sumOp_transversal h Λ Λ' hΛ').1 s hs (Fin n) f hf ht).1, map_sum]
    simp only [form_translate_vacuum h hΛ hs e he, he1]
    obtain ⟨i0, hi0, huniq⟩ := ht 0 Λ'.zero_mem
    rw [Finset.sum_eq_single i0]
    · rw [if_pos (by simpa using hi0)]
    · intro j _ hj
      rw [if_neg]
      intro hjΛ
      exact hj (huniq j (by simpa using hjΛ))
    · simp
  rw [map_smul, hes', smul_eq_mul, mul_one]

end GlobalTheory.SphTheta
end

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  atlas_forward_decl GlobalTheory.SphTheta.sumOp_vacuum_lift
end
