import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique

section
open MeasureTheory Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_upq_is_mul_right_invariant : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure <;> assumption)
end

section
namespace GlobalTheory

open Module

open Module in

theorem _root_.GlobalTheory.exists_hyperbolic_completion :
    ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by
  intro E V _ _ _ _ _ _ h hs hn W hW i e he hee heW hdim
  set m := finrank E W with hm
  let b := Module.finBasis E W
  let w : Fin m → V := fun j => (b j : V)
  have hwW : ∀ j, w j ∈ W := fun j => (b j).2
  let u : Fin i ⊕ Fin m → V := Sum.elim e w
  have hw : LinearIndependent E w := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hu : LinearIndependent E u := by
    refine he.sum_type hw ?_
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hxW : x ∈ W := (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwW j)) hx2
    refine hW x hxW fun y hy => ?_
    have hle : Submodule.span E (Set.range e) ≤ LinearMap.ker (h y) :=
      Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact heW a y hy)
    rw [← hs.eq, show h y x = 0 from hle hx1, map_zero]
  let L : V →ₗ[E] (Fin i ⊕ Fin m → E) := LinearMap.pi fun k => h (u k)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨μ, hμ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hz : ∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k = 0 := by
      refine hn.1 _ fun y => ?_
      have h0 : μ (L y) = 0 := hle (LinearMap.mem_range_self L y)
      rw [LinearMap.pi_apply_eq_sum_univ] at h0
      have h1 : h (∑ k, star (μ fun j => if k = j then (1 : E) else 0) • u k) y = ∑ k, L y k • μ fun j => if k = j then (1 : E) else 0 := by
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, L, LinearMap.pi_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [h1, h0]
    have hc0 : ∀ k, μ (fun j => if k = j then (1 : E) else 0) = 0 := fun k => by
      have := Fintype.linearIndependent_iff.mp hu _ hz k
      simpa using this
    apply hμ
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [hc0, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]
  choose g hg using fun a : Fin i => hL fun k => if k = Sum.inl a then (1 : E) else 0
  have hge : ∀ a b, h (e b) (g a) = if b = a then 1 else 0 := fun a b => by
    have := congrFun (hg a) (Sum.inl b)
    simpa [L, u] using this
  have hgw : ∀ a j, h (w j) (g a) = 0 := fun a j => by
    have := congrFun (hg a) (Sum.inr j)
    simpa [L, u] using this
  have hgW : ∀ a, ∀ x ∈ W, h x (g a) = 0 := by
    intro a x hx
    have hx' : x = ∑ j, b.repr ⟨x, hx⟩ j • w j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [hx']
    simp [map_sum, hgw]
  set f : Fin i → V := fun a => g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c with hf
  have hfa : ∀ a, f a = g a - ∑ c, (2⁻¹ * h (g c) (g a)) • e c := fun a => rfl
  have hfe : ∀ a b, h (e b) (f a) = if b = a then 1 else 0 := by
    intro a b
    rw [hfa]
    simp [map_sub, map_sum, hee, hge]
  have hfe' : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs.eq, hfe]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hfW : ∀ a, ∀ x ∈ W, h x (f a) = 0 := by
    intro a x hx
    rw [hfa]
    simp [map_sub, map_sum, hgW a x hx, heW _ x hx]
  have hff : ∀ a b, h (f a) (f b) = 0 := by
    intro a b
    have hs' : starRingEnd E (h (g b) (g a)) = h (g a) (g b) := hs.eq (g b) (g a)
    have h1 : h (f a) (f b) = h (f a) (g b) - 2⁻¹ * h (g a) (g b) := by
      conv_lhs => rw [hfa b]
      simp [map_sub, map_sum, hfe']
    rw [h1, hfa a]
    simp [map_sub, map_sum, hge, hs', map_ofNat]
    ring
  let v : Fin i ⊕ (Fin i ⊕ Fin m) → V := Sum.elim f u
  have hu0 : ∀ c k, h (e c) (u k) = 0 := by
    intro c k
    rcases k with d | j
    · exact hee c d
    · show h (e c) (w j) = 0
      rw [← hs.eq, heW c _ (hwW j)]
      simp
  have hv : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro γ hγ
    simp only [v] at hγ
    rw [Fintype.sum_sum_type] at hγ
    simp only [Sum.elim_inl, Sum.elim_inr] at hγ
    have hfst : ∀ a, γ (Sum.inl a) = 0 := by
      intro a
      have := congrArg (h (e a)) hγ
      simpa [map_add, map_sum, hfe, hu0] using this
    have hrest : ∑ k, γ (Sum.inr k) • u k = 0 := by simpa [hfst] using hγ
    intro k
    rcases k with a | k
    · exact hfst a
    · exact Fintype.linearIndependent_iff.mp hu _ hrest k
  have hspan : Submodule.span E (Set.range v) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (by simp; omega)
  refine ⟨f, hff, hfe', hfW, ?_⟩
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rcases k with a | c | j
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
  · exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨c, rfl⟩))
  · exact Submodule.mem_sup_left (hwW j)

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolic_dual_family_of_finrank_add_two_mul : ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → h.Nondegenerate → ∀ (W : Submodule E V), (∀ x ∈ W, (∀ y ∈ W, h x y = 0) → x = 0) → ∀ (i : ℕ) (e : Fin i → V), LinearIndependent E e → (∀ a b, h (e a) (e b) = 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0) → Module.finrank E W + 2 * i = Module.finrank E V → ∃ f : Fin i → V, (∀ a b, h (f a) (f b) = 0) ∧ (∀ a b, h (f a) (e b) = if a = b then 1 else 0) ∧ (∀ a, ∀ x ∈ W, h x (f a) = 0) ∧ W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ := by
  first | exact @GlobalTheory.exists_hyperbolic_completion | exact GlobalTheory.exists_hyperbolic_completion | (intros; apply GlobalTheory.exists_hyperbolic_completion <;> assumption)
end

section
section
namespace GlobalTheory

theorem finrank_add_two_mul_of_hyperbolic_pairs :
    ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by
  intro E V _ _ _ _ _ h hS W i e f hee hff hfe hW hspan
  classical

  have hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hS.eq (f b) (e a), hfe]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]

  have coeff_e : ∀ (c : Fin i ⊕ Fin i → E) (a : Fin i),
      h (e a) (∑ j, c j • Sum.elim e f j) = c (Sum.inr a) := by
    intro c a
    simp [map_sum, map_smul, Fintype.sum_sum_type, hee, hef]
  have coeff_f : ∀ (c : Fin i ⊕ Fin i → E) (a : Fin i),
      h (f a) (∑ j, c j • Sum.elim e f j) = c (Sum.inl a) := by
    intro c a
    simp [map_sum, map_smul, Fintype.sum_sum_type, hff, hfe]
  have hli : LinearIndependent E (Sum.elim e f) := by
    refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
    rcases j with a | a
    · rw [← coeff_f c a, hc, map_zero]
    · rw [← coeff_e c a, hc, map_zero]
  have hrange : Set.range e ∪ Set.range f = Set.range (Sum.elim e f) :=
    (Set.Sum.elim_range e f).symm
  rw [hrange] at hspan
  set U := Submodule.span E (Set.range (Sum.elim e f)) with hU
  have hinf : W ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨huW, huU⟩ := Submodule.mem_inf.1 hu
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 huU
    have hc : ∀ j, c j = 0 := by
      rintro (a | a)
      · rw [← coeff_f c a, ← hS.eq _ (f a), (hW a _ huW).2, map_zero]
      · rw [← coeff_e c a, ← hS.eq _ (e a), (hW a _ huW).1, map_zero]
    simp [hc]
  have hUdim : Module.finrank E U = 2 * i := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin]
    ring
  refine ⟨by simpa using hli.comp Sum.inl Sum.inl_injective, ?_⟩
  have key := Submodule.finrank_sup_add_finrank_inf_eq W U
  rw [hspan, hinf, finrank_top, finrank_bot, add_zero, hUdim] at key
  exact key.symm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic : ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by
  atlas_forward_decl GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticExt_norm_form_over_algebra : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  first | exact @GlobalTheory.QuadNormBase.norm_form | exact GlobalTheory.QuadNormBase.norm_form | (intros; apply GlobalTheory.QuadNormBase.norm_form <;> assumption)
end

section
open NumberField IsDedekindDomain
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one : ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → {a : (AdeleRing (𝓞 F) F)ˣ | ∃ x y : AdeleRing (𝓞 F) F, (a : AdeleRing (𝓞 F) F) = x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
  first | exact @GlobalTheory.QNorm.norm_form_mem_nhds_one | exact GlobalTheory.QNorm.norm_form_mem_nhds_one | (intros; apply GlobalTheory.QNorm.norm_form_mem_nhds_one <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.QNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ), ¬ IsSquare (δ : F) → ∃ S : Finset (HeightOneSpectrum (𝓞 F)), admitted F S ∧ δ ∈ sUnits F S ∧ ∀ t : Fˣ, (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → t ∈ normSub (algebraMap F (v.adicCompletion F)) (δ : F)) → t ∈ sUnits F S ⊔ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | exact GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub | (intros; apply GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub <;> assumption)
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.QNorm

theorem exists_adele_finite_component (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : AdeleRing (𝓞 F) F →+* v.adicCompletion F, (∀ x, e x = x.2 v) ∧
      ∀ t : F, e (algebraMap F (AdeleRing (𝓞 F) F) t) = algebraMap F (v.adicCompletion F) t :=
  ⟨{ toFun := fun x => x.2 v
     map_one' := rfl
     map_mul' := fun _ _ => rfl
     map_zero' := rfl
     map_add' := fun _ _ => rfl }, fun _ => rfl, fun _ => rfl⟩

theorem exists_infiniteAdele_real_component (F : Type) [Field F] [NumberField F]
    (σ : F →+* ℝ) :
    ∃ e : InfiniteAdeleRing F →+* ℝ,
      ∀ t : F, e (algebraMap F (InfiniteAdeleRing F) t) = σ t := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hφ, rfl⟩
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) _), fun t => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1).symm t)
  refine he.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

open Classical in

noncomputable def adeleOn (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) : AdeleRing (𝓞 F) F :=
  (algebraMap F (InfiniteAdeleRing F) z,
    (⟨fun v => if v ∈ S then algebraMap F (v.adicCompletion F) z else 1, by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := hv
      simp only [if_neg hv', SetLike.mem_coe]
      exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F))

theorem adeleOn_snd_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) z := if_pos hv

theorem adeleOn_snd_of_notMem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (adeleOn F S z).2 v = 1 := if_neg hv

theorem adeleOn_mul_inv (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {z : F} (hz : z ≠ 0) :
    adeleOn F S z * adeleOn F S z⁻¹ = 1 := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext F fun v => ?_)
  · change algebraMap F (InfiniteAdeleRing F) z * algebraMap F (InfiniteAdeleRing F) z⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  · change (adeleOn F S z).2 v * (adeleOn F S z⁻¹).2 v = 1
    by_cases hv : v ∈ S
    · rw [adeleOn_snd_of_mem F S _ hv, adeleOn_snd_of_mem F S _ hv, ← map_mul,
        mul_inv_cancel₀ hz, map_one]
    · rw [adeleOn_snd_of_notMem F S _ hv, adeleOn_snd_of_notMem F S _ hv, mul_one]

theorem div_mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (z t : Fˣ)
    (a b : L) (h : φ (z : F) = φ (t : F) * (a ^ 2 - φ δ * b ^ 2)) : z / t ∈ normSub φ δ := by
  refine ⟨a, b, ?_⟩
  have ht : φ (t : F) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, map_div₀, h]
  field_simp

theorem exists_idele_not_mul_norm : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  intro F _ _ δ hsq
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hsq IsSquare.zero
  obtain ⟨S, hS, hδ, hadj⟩ := GlobalTheory.T.exists_admissible_localNorm_mem_sUnits_sup_globalNorm F (Units.mk0 δ hδ0) hsq
  have hne := sUnits_sup_locNorm_ne_top F (Units.mk0 δ hδ0) S hS hδ hsq
  simp only [Units.val_mk0] at hadj hne
  obtain ⟨z, hz⟩ : ∃ z : Fˣ, z ∉ sUnits F S ⊔ locNorm F δ S := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_top_iff' _ |>.2 hcon)
  refine ⟨Units.mkOfMulEqOne _ _ (adeleOn_mul_inv F S z.ne_zero), fun t x y h => hz ?_⟩
  replace h : adeleOn F S z = algebraMap F (AdeleRing (𝓞 F) F) t *
      (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := h
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at h
    have h1 : algebraMap F (InfiniteAdeleRing F) z = 0 := congrArg Prod.fst h
    exact z.ne_zero ((map_eq_zero _).1 h1)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F,
      (adeleOn F S z).2 v = algebraMap F (v.adicCompletion F) t *
        (a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) := by
    intro v
    obtain ⟨e, he, he'⟩ := exists_adele_finite_component F v
    refine ⟨e x, e y, ?_⟩
    rw [← he, h, map_mul, map_sub, map_mul, map_pow, map_pow, he', he']
  have h1 : Units.mk0 t ht ∈ sUnits F S ⊔ locNorm F δ S := by
    refine sup_le_sup_left (normSub_id_le_locNorm F δ S) _ (hadj _ fun v hv => ?_)
    obtain ⟨a, b, hab⟩ := hfin v
    rw [adeleOn_snd_of_notMem F S _ hv] at hab
    have h2 := div_mem_normSub (algebraMap F (v.adicCompletion F)) δ 1 (Units.mk0 t ht) a b
      (by simpa using hab)
    rwa [one_div, inv_mem_iff] at h2
  have h2 : z / Units.mk0 t ht ∈ locNorm F δ S := by
    refine ⟨Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_,
      Subgroup.mem_iInf.2 fun σ => ?_⟩
    · obtain ⟨a, b, hab⟩ := hfin v
      rw [adeleOn_snd_of_mem F S _ hv] at hab
      exact div_mem_normSub _ δ z (Units.mk0 t ht) a b hab
    · obtain ⟨e, he⟩ := exists_infiniteAdele_real_component F σ
      refine div_mem_normSub σ δ z (Units.mk0 t ht) (e x.1) (e y.1) ?_
      have h3 : algebraMap F (InfiniteAdeleRing F) z = algebraMap F (InfiniteAdeleRing F) t *
          (x.1 ^ 2 - algebraMap F (InfiniteAdeleRing F) δ * y.1 ^ 2) := congrArg Prod.fst h
      have h4 := congrArg e h3
      rwa [map_mul, map_sub, map_mul, map_pow, map_pow, he, he, he] at h4
  have h3 := mul_mem (Subgroup.mem_sup_right (S := sUnits F S) h2) h1
  rwa [div_mul_cancel] at h3

end GlobalTheory.QNorm
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by
  first | exact @GlobalTheory.QNorm.exists_idele_not_mul_norm | exact GlobalTheory.QNorm.exists_idele_not_mul_norm | (intros; apply GlobalTheory.QNorm.exists_idele_not_mul_norm <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Topology

namespace GlobalTheory.VolHeckeCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem infFam_unique {D : D7} {θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ)

theorem allSome_infFam_iff {D : D7} (Q : (D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) → Prop) :
    AllSome (IsInfFam (D := D)) Q ↔ ∃ θ, IsInfFam θ ∧ Q θ :=
  ⟨fun ⟨⟨θ, hθ⟩, h⟩ => ⟨θ, hθ, h θ hθ⟩,
    fun ⟨θ, hθ, h⟩ => ⟨⟨θ, hθ⟩, fun _ hθ' => infFam_unique hθ hθ' ▸ h⟩⟩

theorem infPart_eq (D : D7) : infPart D = UnitaryVolumePairs.infPart D := rfl
theorem finPart_eq (D : D7) : finPart D = UnitaryVolumePairs.finPart D := rfl
theorem idF_eq (D : D7) : idF D = UnitaryVolumePairs.resF D := rfl

theorem isHeckeChar_iff (D : D7) (χ : (AE D)ˣ →* Circle) : IsHeckeChar D χ ↔ χ ∈ UnitaryVolumePairs.HeckeChar D := Iff.rfl

theorem hasInfExp_iff (D : D7) (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a : ℚ) :
    HasInfExp D χ τ a ↔ UnitaryVolumePairs.HasExponent χ τ a := by
  unfold HasInfExp UnitaryVolumePairs.HasExponent
  refine exists_congr fun n => and_congr Iff.rfl ?_
  rw [allSome_infFam_iff]
  refine exists_congr fun θ => and_congr Iff.rfl (forall_congr' fun x => ?_)
  exact ⟨fun h hx => h hx.1 hx.2, fun h h1 h2 => h ⟨h1, h2⟩⟩

theorem unramEverywhere_iff (D : D7) (χ : (AE D)ˣ →* Circle) :
    UnramEverywhere D χ ↔ UnitaryVolumePairs.IsUnramified χ :=
  forall_congr' fun _ => ⟨fun h hx => h hx.1 hx.2.1 hx.2.2, fun h h1 h2 h3 => h ⟨h1, h2, h3⟩⟩

theorem exists_not_fixed (D : D7) : ∃ x, D.sp.cm.sig x ≠ x := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun x => (D.sp.cm.fixed x).1 (h x)
  have h1 : Module.finrank D.host.F D.host.E = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
      ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
  have h2 := D.sp.cm.deg2
  omega

theorem algebraMap_AE_injective (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem resF_injective (D : D7) : Function.Injective (UnitaryVolumePairs.resF D) := fun _ _ h =>
  Units.ext (algebraMap_AE_injective D (congrArg Units.val h))

abbrev normU (D : D7) : (AE D)ˣ →* (AF D.host.F)ˣ := Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)

theorem exists_form (D : D7) : ∃ δ : D.host.F, ¬ IsSquare δ ∧
    (∀ x, UnitaryVolumePairs.resF D (normU D x) = UnitaryVolumePairs.normId D x) ∧
    ∀ a : (AF D.host.F)ˣ, a ∈ (normU D).range ↔
      ∃ x y : AF D.host.F, (a : AF D.host.F) = x ^ 2 - algebraMap D.host.F (AF D.host.F) δ * y ^ 2 := by
  obtain ⟨δ, hδ, h⟩ := GlobalTheory.T.quadraticExt_norm_form_over_algebra D.host.F D.host.E D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
    (exists_not_fixed D)
  obtain ⟨h1, h2⟩ := h (AF D.host.F)
  have hN : ∀ z : AE D, algebraMap (AF D.host.F) (AE D) (Algebra.norm (AF D.host.F) z) =
      z * sigR (AF D.host.F) D.sp.cm.sig z := fun z => by
    obtain ⟨x, y, e1, e2⟩ := h1 z
    rw [e1, e2]
  refine ⟨δ, hδ, fun x => Units.ext (hN x), fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, y, e1, -⟩ := h1 z
    exact ⟨x, y, e1⟩
  · rintro ⟨x, y, e⟩
    obtain ⟨z, hz⟩ := h2 x y
    rw [← e] at hz
    have hu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ a.isUnit.map _)
    refine ⟨hu.unit, Units.ext (algebraMap_AE_injective D ?_)⟩
    exact (hN z).trans hz

theorem normGroup_eq (D : D7) : UnitaryVolumePairs.normGroup D = (UnitaryVolumePairs.ratF D).range ⊔ (normU D).range := by
  obtain ⟨-, -, h, -⟩ := exists_form D
  unfold UnitaryVolumePairs.normGroup
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, resF_injective D ((h x).trans hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, (h x).symm⟩

theorem isOpen_normGroup (D : D7) : IsOpen (UnitaryVolumePairs.normGroup D : Set (AF D.host.F)ˣ) := by
  obtain ⟨δ, hδ, -, h⟩ := exists_form D
  have h0 : δ ≠ 0 := fun e => hδ (e ▸ IsSquare.zero)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (GlobalTheory.T.quadraticForm_ideleValues_mem_nhds_one D.host.F δ h0) fun a ha => ?_)
  rw [normGroup_eq]
  exact Subgroup.mem_sup_right ((h a).2 ha)

theorem normGroup_ne_top (D : D7) : UnitaryVolumePairs.normGroup D ≠ ⊤ := by
  obtain ⟨δ, hδ, -, h⟩ := exists_form D
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare D.host.F δ hδ
  intro e
  have hm : a ∈ UnitaryVolumePairs.normGroup D := e ▸ Subgroup.mem_top a
  rw [normGroup_eq] at hm
  obtain ⟨_, ⟨t, rfl⟩, n, hn, rfl⟩ := Subgroup.mem_sup.1 hm
  obtain ⟨x, y, e⟩ := (h n).1 hn
  exact ha t x y (by rw [Units.val_mul, e]; rfl)

theorem sq_mem_normGroup (D : D7) (a : (AF D.host.F)ˣ) : a * a ∈ UnitaryVolumePairs.normGroup D := by
  obtain ⟨δ, -, -, h⟩ := exists_form D
  rw [normGroup_eq]
  exact Subgroup.mem_sup_right ((h _).2 ⟨a, 0, by simp [pow_two]⟩)

theorem isEta_iff_normGroup (D : D7) (η : (AF D.host.F)ˣ →* Circle) :
    IsEta D η ↔ UnitaryVolumePairs.normGroup D ≤ η.ker ∧ η ≠ 1 := by
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨?_, h3⟩
    rw [normGroup_eq]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩; exact h1 a
    · rintro _ ⟨a, rfl⟩; exact h2 a
  · rintro ⟨h, h3⟩
    refine ⟨?_, fun a => h ?_, fun x => h ?_, h3⟩
    · refine continuous_of_continuousAt_one η ?_
      refine (continuousAt_const (y := (1 : Circle))).congr ?_
      filter_upwards [(isOpen_normGroup D).mem_nhds (one_mem _)] with a ha
      exact (h ha).symm
    · rw [normGroup_eq]; exact Subgroup.mem_sup_left ⟨a, rfl⟩
    · rw [normGroup_eq]; exact Subgroup.mem_sup_right ⟨x, rfl⟩

theorem circle_eq_neg_one {z : Circle} (h : z * z = 1) (h1 : z ≠ 1) : (z : ℂ) = -1 := by
  have h2 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h2 with h3 | h3
  · exact absurd (Circle.ext h3) h1
  · exact h3

theorem exists_char_of_not_mem {G : Type} [CommGroup G] (N : Subgroup G) (hN : ∀ a, a * a ∈ N) (a : G)
    (ha : a ∉ N) : ∃ η : G →* Circle, N ≤ η.ker ∧ η a ≠ 1 := by
  have hne : (QuotientGroup.mk a : G ⧸ N) ≠ 1 := fun e => ha ((QuotientGroup.eq_one_iff a).1 e)
  have h2 : ∀ x : Additive (G ⧸ N), 2 • x = 0 := fun x => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk g : G ⧸ N) := by rw [hg]; rfl
    rw [hx, two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (hN g)]
    rfl
  letI : Module (ZMod 2) (Additive (G ⧸ N)) := AddCommGroup.zmodModule h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2)
    (x := (Additive.ofMul (QuotientGroup.mk a : G ⧸ N))) hne
  refine ⟨{ toFun := fun g => ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N)))
            map_one' := by simp
            map_mul' := fun g g' => by
              rw [QuotientGroup.mk_mul, ofMul_mul, map_add, AddChar.map_add_eq_mul] }, fun g hg => ?_, ?_⟩
  · show ZMod.toCircle (φ (Additive.ofMul (QuotientGroup.mk g : G ⧸ N))) = 1
    rw [(QuotientGroup.eq_one_iff g).2 hg]
    simp
  · intro e
    apply hφ
    apply ZMod.injective_toCircle
    rw [AddChar.map_zero_eq_one]
    exact e

theorem exists_isEta_ne_one (D : D7) {a : (AF D.host.F)ˣ} (ha : a ∉ UnitaryVolumePairs.normGroup D) :
    ∃ η, IsEta D η ∧ η a ≠ 1 := by
  obtain ⟨η, h1, h2⟩ := exists_char_of_not_mem _ (sq_mem_normGroup D) a ha
  exact ⟨η, (isEta_iff_normGroup D η).2 ⟨h1, fun e => h2 (by rw [e]; rfl)⟩, h2⟩

theorem exists_isEta (D : D7) : ∃ η, IsEta D η := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ UnitaryVolumePairs.normGroup D := by
    by_contra h
    push Not at h
    exact normGroup_ne_top D (eq_top_iff.2 fun a _ => h a)
  obtain ⟨η, h, -⟩ := exists_isEta_ne_one D ha
  exact ⟨η, h⟩

theorem eta_of_mem {D : D7} {a : (AF D.host.F)ˣ} (ha : a ∈ UnitaryVolumePairs.normGroup D) : UnitaryVolumePairs.eta D a = 1 := if_pos ha
theorem eta_of_not_mem {D : D7} {a : (AF D.host.F)ˣ} (ha : a ∉ UnitaryVolumePairs.normGroup D) : UnitaryVolumePairs.eta D a = -1 := if_neg ha

theorem IsEta_mul_self {D : D7} {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) :
    η a * η a = 1 := by
  rw [← map_mul]
  exact ((isEta_iff_normGroup D η).1 h).1 (sq_mem_normGroup D a)

theorem coe_eq_eta_iff {D : D7} {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) :
    (∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a) ↔ η.ker = UnitaryVolumePairs.normGroup D := by
  constructor
  · intro e
    refine le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1
    by_contra hn
    have h1 := e a
    rw [eta_of_not_mem hn, show η a = 1 from ha] at h1
    norm_num at h1
  · intro e a
    by_cases ha : a ∈ UnitaryVolumePairs.normGroup D
    · rw [eta_of_mem ha, show η a = 1 from ((isEta_iff_normGroup D η).1 h).1 ha]; rfl
    · rw [eta_of_not_mem ha]
      exact circle_eq_neg_one (IsEta_mul_self h a) fun e1 => ha (e ▸ e1)

theorem eq_of_coe_eq_eta {D : D7} {ψ η : (AF D.host.F)ˣ →* Circle} (e : ∀ a, (ψ a : ℂ) = UnitaryVolumePairs.eta D a)
    (h : IsEta D η) : η = ψ := by
  obtain ⟨h1, h2⟩ := (isEta_iff_normGroup D η).1 h
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact h2 (MonoidHom.ext hh)
  have hbn : b ∉ UnitaryVolumePairs.normGroup D := fun hm => hb (h1 hm)
  refine MonoidHom.ext fun a => Circle.ext ?_
  rw [e a]
  by_cases ha : a ∈ UnitaryVolumePairs.normGroup D
  · rw [eta_of_mem ha, show η a = 1 from h1 ha]; rfl
  · rw [eta_of_not_mem ha]
    have hab : a * b ∈ UnitaryVolumePairs.normGroup D := by
      by_contra hn
      have h3 := e (a * b)
      rw [map_mul, Circle.coe_mul, e a, e b, eta_of_not_mem ha, eta_of_not_mem hbn, eta_of_not_mem hn] at h3
      norm_num at h3
    have h4 : η a * η b = 1 := by rw [← map_mul]; exact h1 hab
    refine circle_eq_neg_one (IsEta_mul_self h a) fun e1 => hb ?_
    rwa [e1, one_mul] at h4

theorem isEta_unique_iff (D : D7) (η : (AF D.host.F)ˣ →* Circle) :
    (IsEta D η ∧ ∀ η', IsEta D η' → η' = η) ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a := by
  constructor
  · rintro ⟨h, hu⟩
    refine (coe_eq_eta_iff h).2 (le_antisymm (fun a ha => ?_) ((isEta_iff_normGroup D η).1 h).1)
    by_contra hn
    obtain ⟨η', h', h1⟩ := exists_isEta_ne_one D hn
    exact h1 (hu η' h' ▸ ha)
  · intro e
    obtain ⟨η₀, h₀⟩ := exists_isEta D
    exact ⟨eq_of_coe_eq_eta e h₀ ▸ h₀, fun η' h' => eq_of_coe_eq_eta e h'⟩

theorem isEta_iff_of_index_two (D : D7) (h2 : (UnitaryVolumePairs.normGroup D).index = 2) (η : (AF D.host.F)ˣ →* Circle) :
    IsEta D η ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a := by
  refine ⟨fun h => (coe_eq_eta_iff h).2 ?_, fun e => ((isEta_unique_iff D η).2 e).1⟩
  obtain ⟨h1, h3⟩ := (isEta_iff_normGroup D η).1 h
  refine le_antisymm (fun a ha => ?_) h1
  by_contra hn
  refine h3 (MonoidHom.ext fun b => ?_)
  by_cases hb : b ∈ UnitaryVolumePairs.normGroup D
  · exact h1 hb
  · have hab : a * b ∈ UnitaryVolumePairs.normGroup D := (Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hn hb)
    have h4 : η a * η b = 1 := by rw [← map_mul]; exact h1 hab
    rwa [show η a = 1 from ha, one_mul] at h4

theorem resEta_iff (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) :
    ResEta D χ n ↔ UnitaryVolumePairs.RestrictsToEtaPow χ n := by
  have hsq : ∀ a, UnitaryVolumePairs.eta D a ^ 2 = 1 := fun a => by
    unfold UnitaryVolumePairs.eta
    split_ifs <;> norm_num
  have hsq' : ∀ η, IsEta D η → ∀ a, η a ^ 2 = 1 := fun η h a => by rw [pow_two]; exact IsEta_mul_self h a
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · constructor
    · rintro ⟨⟨η, hη⟩, h⟩ a
      rw [pow_mul, hsq, one_pow, ← idF_eq, h η hη a, pow_mul, hsq' η hη, one_pow]
      rfl
    · intro h
      refine ⟨exists_isEta D, fun η hη a => Circle.ext ?_⟩
      rw [idF_eq, h a, pow_mul, hsq, one_pow, pow_mul, hsq' η hη, one_pow]
      rfl
  · constructor
    · rintro ⟨⟨η, hη⟩, h⟩ a
      have hu : ∀ η', IsEta D η' → η' = χ.comp (idF D) := fun η' h' => MonoidHom.ext fun b => by
        rw [MonoidHom.comp_apply, h η' h' b, pow_succ, pow_mul, hsq' η' h', one_pow, one_mul]
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
      exact (isEta_unique_iff D (χ.comp (idF D))).1 ⟨hu η hη ▸ hη, hu⟩ a
    · intro h
      refine ⟨exists_isEta D, fun η hη a => ?_⟩
      have e : ∀ b, ((χ.comp (idF D)) b : ℂ) = UnitaryVolumePairs.eta D b := fun b => by
        have hb := h b
        rwa [pow_succ, pow_mul, hsq, one_pow, one_mul] at hb
      rw [pow_succ, pow_mul, hsq' η hη, one_pow, one_mul, eq_of_coe_eq_eta e hη]
      rfl

def colVec {D : D7} (V : HSp D) {i : ℕ} (C : Matrix (Fin V.rank) (Fin i) D.host.E) (a : Fin i) : V.V :=
  V.frame.equivFun.symm (C.transpose a)

theorem gram_entry {D : D7} (V : HSp D) {i j : ℕ} (M : Matrix (Fin V.rank) (Fin i) D.host.E)
    (N : Matrix (Fin V.rank) (Fin j) D.host.E) (a : Fin i) (b : Fin j) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N) a b = V.hT (colVec V M a) (colVec V N b) := by
  simp only [colVec, Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, Matrix.mul_apply, Formalism.UG.cT, HSpace.gram, Matrix.transpose_apply, Matrix.map_apply,
    smul_eq_mul, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
  have e : (D.sp.cm.sig : D.host.E →+* D.host.E) (M r a) = starRingEnd D.host.E (M r a) := rfl
  rw [e]
  ring

theorem colVec_frameMat {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) (c : Fin V'.rank) :
    colVec V (frameMat V V' ι) c = ι (V'.frame c) := by
  apply V.frame.equivFun.injective
  funext r
  simp [colVec, frameMat, LinearMap.toMatrix_apply]

theorem hT_swap {D : D7} (V : HSp D) {x y : V.V} (h : V.hT x y = 0) : V.hT y x = 0 := by
  rw [← V.herm.eq x y, h, map_zero]

theorem isomEmb_injective {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V} (h : HSpace.IsIsomEmb V' V ι) :
    Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply V'.nondeg.1
  intro y
  rw [← h x y, hx]
  simp

theorem isIsoSub_iff {D : D7} (V : HSp D) {i : ℕ} (C : Matrix (Fin V.rank) (Fin i) D.host.E) :
    IsIsoSub V C ↔ LinearIndependent D.host.E (colVec V C) ∧ ∀ a b, V.hD (colVec V C a) (colVec V C b) = 0 := by
  refine and_congr ?_ ⟨fun h a b => ?_, fun h => ?_⟩
  · exact (LinearMap.linearIndependent_iff_of_injOn V.frame.equivFun.symm.toLinearMap
      V.frame.equivFun.symm.injective.injOn).symm
  · rw [HSpace.hD, ← gram_entry, h]; rfl
  · refine Matrix.ext fun a b => ?_
    rw [gram_entry]
    exact h b a

theorem orth_iff {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {i : ℕ}
    (C : Matrix (Fin V.rank) (Fin i) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * C = 0 ↔
      ∀ a, ∀ x ∈ LinearMap.range ι, V.hT x (colVec V C a) = 0 := by
  constructor
  · rintro h a _ ⟨x, rfl⟩
    apply hT_swap
    have e : (V.hT (colVec V C a)).comp ι = 0 := V'.frame.ext fun c => by
      have h1 := gram_entry V (frameMat V V' ι) C c a
      rw [h, colVec_frameMat] at h1
      exact hT_swap V h1.symm
    exact LinearMap.congr_fun e x
  · intro h
    refine Matrix.ext fun c a => ?_
    rw [gram_entry, colVec_frameMat]
    exact h a _ ⟨_, rfl⟩

theorem isWittLower_iff {D : D7} (V V' : HSp D) (i : ℕ) : IsWittLower V V' i ↔ UnitaryVolumePairs.IsMinusHyp V i V' := by
  constructor
  · rintro ⟨hr, ι, hι, C, hC, hO⟩
    obtain ⟨h1, h2⟩ := (isIsoSub_iff V C).1 hC
    have h3 := (orth_iff V V' ι C).1 hO
    have hW : ∀ x ∈ LinearMap.range ι, (∀ y ∈ LinearMap.range ι, V.hT x y = 0) → x = 0 := by
      rintro _ ⟨x, rfl⟩ hx
      rw [V'.nondeg.1 x fun y => (hι x y).symm.trans (hx _ ⟨y, rfl⟩), map_zero]
    obtain ⟨f, f1, f2, f3, f4⟩ := GlobalTheory.T.exists_hyperbolic_dual_family_of_finrank_add_two_mul D.host.E V.V V.hT V.herm V.nondeg (LinearMap.range ι) hW i
      (colVec V C) h1 (fun a b => h2 b a) h3
      (by rw [LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq, hr])
    refine ⟨ι, colVec V C, f, hι, h2, fun a b => f1 b a, fun a b => ?_, fun a x => ⟨?_, ?_⟩, f4⟩
    · rw [HSpace.hD, f2 b a]
      simp only [eq_comm]
    · exact hT_swap V (h3 a _ ⟨x, rfl⟩)
    · exact hT_swap V (f3 a _ ⟨x, rfl⟩)
  · rintro ⟨ι, e, f, hι, h1, h2, h3, h4, h5⟩
    obtain ⟨k1, k2⟩ := GlobalTheory.T.linearIndependent_and_finrank_add_two_mul_of_hyperbolic D.host.E V.V V.hT V.herm (LinearMap.range ι) i e f (fun a b => h1 b a)
      (fun a b => h2 b a) (fun a b => by
        have h6 := h3 b a
        rw [HSpace.hD] at h6
        rw [h6]
        simp only [eq_comm])
      (by
        rintro a _ ⟨x, rfl⟩
        exact ⟨hT_swap V (h4 a x).1, hT_swap V (h4 a x).2⟩) h5
    have hc : colVec V (Matrix.of fun r a => V.frame.equivFun (e a) r) = e :=
      funext fun a => V.frame.equivFun.symm_apply_apply (e a)
    refine ⟨?_, ι, hι, Matrix.of fun r a => V.frame.equivFun (e a) r, ?_, ?_⟩
    · rwa [LinearMap.finrank_range_of_inj (isomEmb_injective hι), V'.rank_eq, V.rank_eq] at k2
    · rw [isIsoSub_iff, hc]
      exact ⟨k1, h1⟩
    · rw [orth_iff, hc]
      rintro a _ ⟨x, rfl⟩
      exact hT_swap V (h4 a x).1

theorem idem_mul {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {ε : A} (hε : ε * ε = ε)
    (X Y X' Y' : Matrix n n A) :
    (ε • X + (1 - ε) • Y) * (ε • X' + (1 - ε) • Y') = ε • (X * X') + (1 - ε) • (Y * Y') := by
  have h1 : ε * (1 - ε) = 0 := by linear_combination -hε
  have h2 : (1 - ε) * ε = 0 := by linear_combination -hε
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem exists_cut {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (J : Matrix n n A)
    {ε : A} (hε : ε * ε = ε) (hσ : σ ε = ε) (h : GL n A) (hh : h ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, (k : Matrix n n A) = ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A) := by
  have hs : ∀ X : Matrix n n A, ε • X + (1 - ε) • X = X := fun X => by rw [← add_smul]; simp
  refine ⟨⟨ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A),
    ε • (1 : Matrix n n A) + (1 - ε) • ((h⁻¹ : GL n A) : Matrix n n A), ?_, ?_⟩, ?_, rfl⟩
  · rw [idem_mul hε, Units.mul_inv, mul_one, hs]
  · rw [idem_mul hε, Units.inv_mul, mul_one, hs]
  · have hc : Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) =
        ε • (1 : Matrix n n A) + (1 - ε) • Formalism.UG.cT σ (h : Matrix n n A) := by
      refine Matrix.ext fun i j => ?_
      by_cases e : i = j
      · subst e; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne e, Matrix.one_apply_ne' e]
    show Formalism.UG.cT σ (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) * J *
      (ε • (1 : Matrix n n A) + (1 - ε) • (h : Matrix n n A)) = J
    have hh' : Formalism.UG.cT σ (h : Matrix n n A) * J * (h : Matrix n n A) = J := hh
    rw [hc]
    nth_rewrite 1 [← hs J]
    rw [idem_mul hε, idem_mul hε, hh', one_mul, mul_one, hs]

theorem map_cut_one {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (φ : A →+* B) {ε : A}
    (h : φ ε = 1) (X : Matrix n n A) (i j : n) :
    φ ((ε • (1 : Matrix n n A) + (1 - ε) • X) i j) = (1 : Matrix n n B) i j := by
  by_cases e : i = j
  · subst e; simp [h]
  · simp [h, Matrix.one_apply_ne e]

theorem map_cut_zero {A B : Type} [CommRing A] [CommRing B] {n : Type} [DecidableEq n] (φ : A →+* B) {ε : A}
    (h : φ ε = 0) (X : Matrix n n A) (i j : n) :
    φ ((ε • (1 : Matrix n n A) + (1 - ε) • X) i j) = φ (X i j) := by
  simp [h]

theorem finMat_eq {D : D7} (V : HSp D) (h : GA D V) : finMat D.sp.cm.sig V.gram h = (finHom V h).1 := rfl

theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    infMat D.sp.cm.sig V.gram θ h = ((infHom V h).1).map θ := rfl

theorem exists_finite_part {D : D7} (V : HSp D) (h : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V h := by
  let ε : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)
  have hε : ε * ε = ε := by
    simp only [ε, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_one _) (mul_zero _)
  have hσ : sigR (AF D.host.F) D.sp.cm.sig ε = ε := by simp [ε, sigR]
  have hi : infPart D ε = 1 := by
    simp only [ε, infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hf : finPart D ε = 0 := by
    simp only [ε, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact TensorProduct.zero_tmul _ _
  obtain ⟨k, hk, e⟩ := exists_cut (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram) hε hσ (matHom V h) h.2
  refine ⟨⟨k, hk⟩, Units.ext (Matrix.ext fun i j => ?_), Units.ext (Matrix.ext fun i j => ?_)⟩
  · show infPart D (k.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j
    rw [e]
    exact map_cut_one (infPart D) hi _ i j
  · show finPart D (k.1 i j) = finPart D ((matHom V h).1 i j)
    rw [e]
    exact map_cut_zero (finPart D) hf _ i j

theorem volBox_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {P Q : ℕ}
    (A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ) (B : D.what₂.Tau → Set (UpqT P Q)) :
    UnitaryVolumePairs.volBox θ V A B = {h : GA D V | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
                       (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
  ext h
  constructor
  · rintro ⟨k, ⟨hk, hl, -⟩, g, hg, rfl, hb⟩
    have e1 : finHom V (k * g) = finHom V k := by rw [map_mul, show finHom V g = 1 from hg, mul_one]
    have e2 : infHom V (k * g) = infHom V g := by rw [map_mul, show infHom V k = 1 from hk, one_mul]
    refine ⟨fun y => ?_, fun ρ => ?_⟩
    · rw [finMat_eq, e1]; exact hl y
    · rw [infMat_eq, e2]; exact hb ρ
  · rintro ⟨hl, hb⟩
    obtain ⟨k, hk, e⟩ := exists_finite_part V h
    refine ⟨k, ⟨hk, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, k⁻¹ * h, ?_, by group, fun ρ => ?_⟩
    · rw [finMat_eq, e]; exact hl y
    · show finHom V (k⁻¹ * h) = 1
      rw [map_mul, map_inv, e, inv_mul_cancel]
    · rw [infMat_eq, map_mul, map_inv, show infHom V k = 1 from hk, inv_one, one_mul]
      exact hb ρ

theorem gram_det_ne_zero {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := V.nondeg.2 _ fun x => by
    apply hT_swap
    have e2 : V.hT (V.frame.equivFun.symm v) = 0 := V.frame.ext fun c => by
      apply hT_swap
      have h2 := congrFun e c
      simpa [Matrix.mulVec, dotProduct, HSpace.gram, Module.Basis.equivFun_symm_apply, mul_comm] using h2
    rw [e2]; rfl
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

theorem exists_change {P Q n : ℕ} (hn : P + Q = n) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.det ≠ 0)
    (A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G)
    (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) : ∃ u : UpqT P Q, A' = UpqT.mat u * A := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have e : Fin n ≃ Fin P ⊕ Fin Q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hl : ∀ X : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ, Xᴴ * Formalism.UG.Jpq P Q * X = G →
      (G⁻¹ * Xᴴ * Formalism.UG.Jpq P Q) * X = 1 := fun X hX => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hX, Matrix.nonsing_inv_mul _ hu]
  set L := G⁻¹ * Aᴴ * Formalism.UG.Jpq P Q
  set L' := G⁻¹ * A'ᴴ * Formalism.UG.Jpq P Q
  have l1 : L * A = 1 := hl A hA
  have l2 : L' * A' = 1 := hl A' hA'
  have r1 : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 l1
  have r2 : A' * L' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 l2
  refine ⟨(⟨⟨A' * L, A * L', ?_, ?_⟩, ?_⟩ : Formalism.UG.Upq P Q), ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, l1, Matrix.one_mul, r2]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L', l2, Matrix.one_mul, r1]
  · show (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q
    calc (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
          rw [hA', ← hA, Matrix.conjTranspose_mul A L]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [r1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · show A' = A' * L * A
    rw [Matrix.mul_assoc, l1, Matrix.mul_one]

theorem measurableMul_UpqT (P Q : ℕ) : MeasurableMul (UpqT P Q) := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  infer_instance

theorem isProductForm_change {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    {P Q : ℕ} {A A' : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin V.rank) ℂ} (hA : UnitaryVolumePairs.IsRealFrames V P Q A)
    (hA' : UnitaryVolumePairs.IsRealFrames V P Q A') {μ : Measure (GA D V)} (h : UnitaryVolumePairs.IsProductForm θ V A μ) :
    UnitaryVolumePairs.IsProductForm θ V A' μ := by
  have hG : ∀ ρ, (gramAt D V ρ).det ≠ 0 := fun ρ => by
    have e := (tauE D ρ).map_det V.gram
    rw [RingHom.mapMatrix_apply] at e
    rw [gramAt, ← e]
    exact (map_ne_zero _).2 (gram_det_ne_zero V)
  choose u hu using fun ρ => exists_change hA.1 _ (hG ρ) (A ρ) (A' ρ) (hA.2 ρ) (hA'.2 ρ)
  haveI := measurableMul_UpqT P Q
  haveI := D.cd.haar P Q
  haveI := GlobalTheory.T.haar_upq_is_mul_right_invariant P Q (D.cd.cd P Q) (D.cd.haar P Q)
  intro B hB
  have hm : ∀ ρ, MeasurableSet ((fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ)) := fun ρ =>
    measurable_mul_const _ (measurable_const_mul _ (hB ρ))
  have h1 := h _ hm
  simp only [measure_preimage_mul_right, measure_preimage_mul] at h1
  rw [← h1]
  congr 1
  have key : ∀ ρ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), (∃ b ∈ B ρ, UpqT.mat b * A' ρ = A' ρ * g) ↔
      ∃ b ∈ (fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ), UpqT.mat b * A ρ = A ρ * g := fun ρ g => by
    have e2 : UpqT.mat (u ρ)⁻¹ * UpqT.mat (u ρ) = 1 := by
      rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_one]
    constructor
    · rintro ⟨b, hb, e⟩
      refine ⟨(u ρ)⁻¹ * b * u ρ, by simpa [mul_assoc] using hb, ?_⟩
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Matrix.mul_assoc, ← hu ρ,
        Matrix.mul_assoc, e, hu ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    · rintro ⟨b, hb, e⟩
      refine ⟨_, hb, ?_⟩
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.UpqT_mat_mul, hu ρ, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Matrix.mul_assoc (UpqT.mat (u ρ)⁻¹), e2, Matrix.one_mul, e, Matrix.mul_assoc]
  simp only [UnitaryVolumePairs.volBox, key]

theorem isVolMeasG_iff {D : D7} (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)) :
    P + Q = V.rank ∧ IsVolMeasG D V (fun _ => P) (fun _ => Q) μ ↔ UnitaryVolumePairs.IsVolMeasure V P Q μ := by
  unfold IsVolMeasG UnitaryVolumePairs.IsVolMeasure
  rw [allSome_infFam_iff]
  constructor
  · rintro ⟨hr, hμ, θ, hθ, ⟨A, hA⟩, h⟩
    refine ⟨hμ, θ, hθ, A, ⟨hr, hA⟩, fun B hB => ?_⟩
    rw [volBox_eq]
    exact h A hA B hB
  · rintro ⟨hμ, θ, hθ, A, hA, h⟩
    refine ⟨hA.1, hμ, θ, hθ, ⟨A, hA.2⟩, fun A' hA' B hB => ?_⟩
    have h1 := isProductForm_change θ V hA ⟨hA.1, hA'⟩ h B hB
    rw [volBox_eq] at h1
    exact h1

theorem sig_add_of_sigOK {D : D7} {V : HSp D} (h : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).1 + (V.sig τ).2 = V.rank := by
  obtain ⟨e, -⟩ := h τ
  simpa using (Fintype.card_congr e).symm

theorem isVolMeasG_iff_of_kind {D : D7} {V : HSp D} {P Q : ℕ} (h : UnitaryVolumePairs.IsOfKind V P Q) (μ : Measure (GA D V)) :
    IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ ↔
      UnitaryVolumePairs.IsVolMeasure V P Q μ := by
  have hr : P + Q = V.rank := by simpa [h.2] using sig_add_of_sigOK h.1 D.host.φ₀
  rw [← isVolMeasG_iff]
  simp only [h.2, hr, true_and]

theorem isVolPair_iff {D : D7} {V : HSp D} {P Q : ℕ} (h : UnitaryVolumePairs.IsOfKind V P Q) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) : IsVolPair D V μ 𝓕 ↔ UnitaryVolumePairs.IsVolPair V P Q μ 𝓕 :=
  and_congr (isVolMeasG_iff_of_kind h μ) Iff.rfl

theorem isFundamentalDomain_of_haar {D : D7} (V : HSp D) {μ μ' : Measure (GA D V)} (h : μ.IsHaarMeasure)
    (h' : μ'.IsHaarMeasure) {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IsFundamentalDomain (GQ V) 𝓕 μ' := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.lcsc_adelic_unitary_group D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  exact h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure μ' μ)

def VolTieAt (D : D7) (W : HSp D) : Prop :=
  AllSome (IsVolMeasG D W (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2)) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (GQ W) 𝓕 μ) fun 𝓕 => μ 𝓕 = ENNReal.ofReal (D.vol W)

theorem volumeTie_iff_at (D : D7) :
    (∀ W : HSp D, W.SigOK → (∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) ↔ UnitaryVolumePairs.VolumeTie D := by
  constructor
  · intro h V P Q hk
    obtain ⟨⟨μ, hμ⟩, h1⟩ := h V hk.1 ⟨_, hk.2⟩
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := h1 μ hμ
    refine ⟨⟨μ, 𝓕, (isVolPair_iff hk μ 𝓕).1 ⟨hμ, h𝓕⟩⟩, fun μ' 𝓕' h' => ?_⟩
    obtain ⟨h2, h3⟩ := (isVolPair_iff hk μ' 𝓕').2 h'
    exact (h1 μ' h2).2 𝓕' h3
  · rintro h V hV ⟨⟨P, Q⟩, hs⟩
    have hk : UnitaryVolumePairs.IsOfKind V P Q := ⟨hV, hs⟩
    obtain ⟨⟨μ, 𝓕, h0⟩, h1⟩ := h V P Q hk
    obtain ⟨h2, h3⟩ := (isVolPair_iff hk μ 𝓕).2 h0
    exact ⟨⟨μ, h2⟩, fun μ' h' => ⟨⟨𝓕, isFundamentalDomain_of_haar V h2.1 h'.1 h3⟩,
      fun 𝓕' h4 => h1 μ' 𝓕' ((isVolPair_iff hk μ' 𝓕').1 ⟨h', h4⟩)⟩⟩

theorem volumeTie_of_volTieG (D : D7) (h : VolTieG D) : UnitaryVolumePairs.VolumeTie D :=
  (volumeTie_iff_at D).1 fun W hW _ => h W hW

theorem volTieG_iff (D : D7) : VolTieG D ↔
    UnitaryVolumePairs.VolumeTie D ∧ ∀ W : HSp D, W.SigOK → (¬ ∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W := by
  refine ⟨fun h => ⟨volumeTie_of_volTieG D h, fun W hW _ => h W hW⟩, fun ⟨h1, h2⟩ W hW => ?_⟩
  by_cases hs : ∃ s, ∀ τ, W.sig τ = s
  · exact (volumeTie_iff_at D).2 h1 W hW hs
  · exact h2 W hW hs

theorem compare (D : D7) :
    (AE D = UnitaryVolumePairs.AE D ∧ infPart D = UnitaryVolumePairs.infPart D ∧ finPart D = UnitaryVolumePairs.finPart D ∧ idF D = UnitaryVolumePairs.resF D ∧
      intAE D = UnitaryVolumePairs.intAfE D) ∧
    (∀ χ : (AE D)ˣ →* Circle, (IsHeckeChar D χ ↔ χ ∈ UnitaryVolumePairs.HeckeChar D) ∧
      (∀ τ a, HasInfExp D χ τ a ↔ UnitaryVolumePairs.HasExponent χ τ a) ∧
      (UnramEverywhere D χ ↔ UnitaryVolumePairs.IsUnramified χ) ∧
      ∀ n, ResEta D χ n ↔ UnitaryVolumePairs.RestrictsToEtaPow χ n) ∧
    (∀ η : (AF D.host.F)ˣ →* Circle, (IsEta D η ↔ UnitaryVolumePairs.normGroup D ≤ η.ker ∧ η ≠ 1) ∧
      ((IsEta D η ∧ ∀ η', IsEta D η' → η' = η) ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a) ∧
      ((UnitaryVolumePairs.normGroup D).index = 2 → (IsEta D η ↔ ∀ a, (η a : ℂ) = UnitaryVolumePairs.eta D a))) ∧
    (∀ (V : HSp D) (i : ℕ) (C : Matrix (Fin V.rank) (Fin i) D.host.E), IsIsoSub V C ↔
      LinearIndependent D.host.E (colVec V C) ∧ ∀ a b, V.hD (colVec V C a) (colVec V C b) = 0) ∧
    (∀ (V V' : HSp D) (i : ℕ), IsWittLower V V' i ↔ UnitaryVolumePairs.IsMinusHyp V i V') ∧
    (∀ (V : HSp D) (P Q : ℕ) (μ : Measure (GA D V)),
      (P + Q = V.rank ∧ IsVolMeasG D V (fun _ => P) (fun _ => Q) μ ↔ UnitaryVolumePairs.IsVolMeasure V P Q μ) ∧
      (UnitaryVolumePairs.IsOfKind V P Q → ∀ 𝓕, IsVolPair D V μ 𝓕 ↔ UnitaryVolumePairs.IsVolPair V P Q μ 𝓕)) ∧
    ((∀ W : HSp D, W.SigOK → (∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) ↔ UnitaryVolumePairs.VolumeTie D) ∧
    (VolTieG D ↔
      UnitaryVolumePairs.VolumeTie D ∧ ∀ W : HSp D, W.SigOK → (¬ ∃ s, ∀ τ, W.sig τ = s) → VolTieAt D W) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun χ => ⟨isHeckeChar_iff D χ, hasInfExp_iff D χ, unramEverywhere_iff D χ, resEta_iff D χ⟩,
    fun η => ⟨isEta_iff_normGroup D η, isEta_unique_iff D η, fun h => isEta_iff_of_index_two D h η⟩,
    fun V _ C => isIsoSub_iff V C, isWittLower_iff,
    fun V P Q μ => ⟨isVolMeasG_iff V P Q μ, fun h 𝓕 => isVolPair_iff h μ 𝓕⟩,
    volumeTie_iff_at D, volTieG_iff D⟩

end GlobalTheory.VolHeckeCompare

end
end
