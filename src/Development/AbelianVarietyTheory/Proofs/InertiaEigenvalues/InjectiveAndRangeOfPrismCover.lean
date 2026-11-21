import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.ProjDescent

section SlopeTestRemainingChoices

variable {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N}

theorem span_top (h : SemiBC u) : Submodule.span B (Set.range u) = ⊤ := by
  obtain ⟨w, -, hw⟩ := h (N ⧸ Submodule.span B (Set.range u)) 0
  have h1 := hw (Submodule.mkQ _) fun x =>
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨x, rfl⟩)
  have h2 := hw 0 fun _ => rfl
  rw [← Submodule.ker_mkQ (Submodule.span B (Set.range u)), h1, ← h2, LinearMap.ker_zero]

theorem induction (h : SemiBC u) (P : N → Prop) (h0 : ∀ x, P (u x)) (h1 : ∀ y z, P y → P z → P (y + z))
    (h2 : ∀ (b : B) y, P y → P (b • y)) (y : N) : P y := by
  have hy : y ∈ Submodule.span B (Set.range u) := by rw [span_top h]; trivial
  induction hy using Submodule.span_induction with
  | mem _ hx => obtain ⟨x, rfl⟩ := hx; exact h0 x
  | zero => rw [← map_zero u]; exact h0 0
  | add y z _ _ hy hz => exact h1 y z hy hz
  | smul b y _ hy => exact h2 b y hy

end SlopeTestRemainingChoices

theorem descent : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  intro A B D _ _ _ f p q hpq hf hfix P _ _ _ _ PB _ _ PD _ _ u u₁ u₂ w hu hw h₁ h₂
  classical
  obtain ⟨n, s, g, -, -, hsg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hx : ∀ x, s (g x) = x := fun x => LinearMap.congr_fun hsg x
  set e : Fin n → P := fun i => s (fun j => if i = j then 1 else 0) with he
  have hdec : ∀ c : Fin n → A, u (s c) = ∑ i, f (c i) • u (e i) := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ s c, map_sum]
    simp only [LinearMap.map_smulₛₗ, e]
  obtain ⟨WB, hWB, -⟩ := hu (Fin n → B)
    { toFun := fun x i => f (g x i)
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  obtain ⟨WD, hWD, -⟩ := hw (Fin n → D)
    { toFun := fun x i => p (f (g x i))
      map_add' := fun x y => funext fun i => by simp
      map_smul' := fun a x => funext fun i => by simp }
  have hWB' : ∀ x i, WB (u x) i = f (g x i) := fun x i => congrFun (hWB x) i
  have hWD' : ∀ x i, WD (w x) i = p (f (g x i)) := fun x i => congrFun (hWD x) i
  have hrec : ∀ z, z = ∑ i, WB z i • u (e i) := by
    intro z
    refine induction hu (fun z => z = ∑ i, WB z i • u (e i)) (fun x => ?_) (fun y z hy hz => ?_)
      (fun b y hy => ?_) z
    · conv_lhs => rw [← hx x]
      rw [hdec]; simp only [hWB']
    · conv_lhs => rw [hy, hz]
      simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · conv_lhs => rw [hy]
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hp : ∀ z i, p (WB z i) = WD (u₁ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, p (WB z i) = WD (u₁ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₁, hWD', hWB']
    · simp only [map_add, Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  have hq : ∀ z i, q (WB z i) = WD (u₂ z) i := by
    intro z
    refine induction hu (fun z => ∀ i, q (WB z i) = WD (u₂ z) i) (fun x i => ?_)
      (fun y z hy hz i => ?_) (fun b y hy i => ?_) z
    · rw [← h₂, hWD', hWB']
      exact (RingHom.congr_fun hpq (g x i)).symm
    · simp only [map_add, Pi.add_apply, hy, hz]
    · simp only [map_smul, LinearMap.map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul, hy]
  refine ⟨fun x y hxy => ?_, fun z hz => ?_⟩
  · have hg : g x = g y := funext fun i => hf (by rw [← hWB', ← hWB', hxy])
    rw [← hx x, ← hx y, hg]
  · have hb : ∀ i, ∃ b, f b = WB z i := fun i => RingHom.mem_range.1 (hfix _ (by rw [hp, hq, hz]))
    choose b hb using hb
    exact ⟨s b, by rw [hdec]; simp only [hb]; exact (hrec z).symm⟩

end GlobalTheory.BSP.ProjDescent
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projective_module_element_descent_equalizer : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), p.comp f = q.comp f → Function.Injective f → (∀ b, p b = q b → b ∈ f.range) → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] (PB : Type) [AddCommGroup PB] [Module B PB] (PD : Type) [AddCommGroup PD] [Module D PD] (u : P →ₛₗ[f] PB) (u₁ : PB →ₛₗ[p] PD) (u₂ : PB →ₛₗ[q] PD) (w : P →ₛₗ[p.comp f] PD), SemiBC u → SemiBC w → (∀ x, w x = u₁ (u x)) → (∀ x, w x = u₂ (u x)) → Function.Injective u ∧ ∀ z, u₁ z = u₂ z → ∃ y, u y = z := by
  atlas_forward_decl GlobalTheory.BSP.ProjDescent.descent
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

noncomputable def matCoordMap {A B : Type} [CommRing A] [CommRing B] {d : ℕ} (q : A →+* B)
    (M : Matrix (Fin d) (Fin d) B) : (Fin d → A) →ₛₗ[q] (Fin d → B) where
  toFun z := M.mulVec fun i => q (z i)
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem Eval.effective_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  intro l _ K bk d S B C N _ _ V h f hc
  obtain ⟨D, p, q, hpo⟩ := hc.stable.po C h
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc
  haveI := V.fin
  haveI := V.proj
  have hcomm : p.f.comp h.f = q.f.comp h.f := congrArg Hom.f hpo.comm
  have key := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f hcomm hinj (hrange D p q hpo) N (Fin d → C.A) (Fin d → D.A)
    (V.v h f) (matCoordMap p.f 1) (matCoordMap q.f (S.ε (p.comp f) (q.comp f))) (V.v (p.comp h) (p.comp f))
    (V.bc h f) (V.bc (p.comp h) (p.comp f))
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (1 : Matrix (Fin d) (Fin d) D.A).mulVec fun i => p.f (V.v h f x i)
      rw [Matrix.one_mulVec]
      funext i
      exact V.v_nat p h f x i)
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (V.v h f x i)
      have e : ∀ a a' : Hom B D, a = a' → V.v a (q.comp f) x = V.v a' (q.comp f) x := by
        intro a a' e; subst e; rfl
      rw [V.v_ε (p.comp h) (p.comp f) (q.comp f) x, e _ _ hpo.comm]
      congr 1
      funext i
      exact V.v_nat q h f x i)
  refine ⟨key.1, fun z hz => key.2 z ?_⟩
  change (1 : Matrix (Fin d) (Fin d) D.A).mulVec (fun i => p.f (z i)) =
    (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)
  rw [Matrix.one_mulVec]
  exact hz D p q hpo.comm

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_range_of_prism_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  atlas_forward_decl GlobalTheory.BSP.Eval.effective_of_cover
end
