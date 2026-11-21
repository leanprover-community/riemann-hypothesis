import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAtlasRefiningCocycle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlas

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_integral_at_index_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ), IntStep A σ 0 := by
  first | exact @GlobalTheory.DRFlag.intStep_zero | exact GlobalTheory.DRFlag.intStep_zero | (intros; apply GlobalTheory.DRFlag.intStep_zero <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_atlas_refining_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (C : Coc X), ∃ A' : Atlas M π ty, (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), A'.FlagAt w u ↔ A.FlagAt w u) ∧ ∃ α : A'.ch.ι → C.A, ∀ a, ⊤ ≤ A'.ch.χ a ⁻¹ᵁ C.B (α a) := by
  first | exact @GlobalTheory.DRFlag.Atlas.exists_refine | exact GlobalTheory.DRFlag.Atlas.exists_refine | (intros; apply GlobalTheory.DRFlag.Atlas.exists_refine <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adapted_of_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → IntStep A σ k → Nonempty (Adapted A σ k) := by
  first | exact @GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted | exact GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted | (intros; apply GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.FrSub

section Lin

variable {K N : Type} [Field K] [AddCommGroup N] [Module K N]

theorem repr_inr_eq_zero_iff {k m : ℕ} (b : Module.Basis (Fin k ⊕ Fin m) K N) (v : N) :
    (∀ j, b.repr v (.inr j) = 0) ↔ v ∈ initSpan K (fun i : Fin k => b (.inl i)) k := by
  have h : initSpan K (fun i : Fin k => b (.inl i)) k = Submodule.span K (b '' Set.range Sum.inl) := by
    rw [initSpan, ← Set.range_comp]
    congr 1
    ext x
    exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩
  rw [h, Module.Basis.mem_span_image]
  constructor
  · rintro h (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)
  · intro h j
    by_contra hne
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 hne)
    exact Sum.inl_ne_inr hi

variable {n m k r : ℕ} (q : N →ₗ[K] (Fin m → K)) {u : Fin n → N} (hj : k + r + 1 ≤ n)

theorem eq_zero_of_sum (hu : LinearIndependent K u) (hq : ∀ v, q v = 0 → v ∈ initSpan K u k) (c : Fin (r + 1) → K)
    (hc : ∑ i, c i • q (u ⟨k + i, by omega⟩) = 0) : c = 0 := by
  let e : Fin (r + 1) → Fin n := fun i => ⟨k + i, by omega⟩
  have he : Function.Injective e := fun i i' h => Fin.ext (by have := congrArg Fin.val h; simp only [e] at this; omega)
  have h1 : ∑ i, c i • u (e i) ∈ initSpan K u k := hq _ (by simpa only [map_sum, map_smul] using hc)
  have h2 : ∑ i, c i • u (e i) ∈ Submodule.span K (u '' {j : Fin n | k ≤ (j : ℕ)}) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e i, Nat.le_add_right _ _, rfl⟩)
  have hd : Disjoint {j : Fin n | (j : ℕ) < k} {j : Fin n | k ≤ (j : ℕ)} :=
    Set.disjoint_left.2 fun j h h' => (not_lt.2 (show k ≤ (j : ℕ) from h')) (show (j : ℕ) < k from h)
  have h3 := Submodule.disjoint_def.1 (hu.disjoint_span_image hd) _ h1 h2
  exact funext (Fintype.linearIndependent_iff.1 (hu.comp e he) c h3)

theorem exists_sum (hq : ∀ v ∈ initSpan K u k, q v = 0) {v : N} (hv : v ∈ initSpan K u (k + r + 1)) :
    ∃ c : Fin (r + 1) → K, ∑ i, c i • q (u ⟨k + i, by omega⟩) = q v := by
  rw [← Submodule.mem_span_range_iff_exists_fun]
  refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap q _)).2 ?_ hv)
  rintro _ ⟨j, hj', rfl⟩
  have hj'' : (j : ℕ) < k + r + 1 := hj'
  show q (u j) ∈ Submodule.span K _
  by_cases h : (j : ℕ) < k
  · rw [hq _ (Submodule.subset_span ⟨j, h, rfl⟩)]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ⟨⟨j - k, by omega⟩, ?_⟩
    have : (⟨k + (j - k), by omega⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simp only [this]

theorem initSpan_full (u : Fin n → N) : initSpan K u n = Submodule.span K (Set.range u) := by
  rw [initSpan]
  congr 1
  ext x
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩⟩

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crdL_apply {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crdL b z h v = crd b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, ← repr_inr_eq_zero_iff]
  exact funext_iff

theorem exists_isFrSub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ), (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → ∀ α : A.ch.ι → D.C.A, (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ Sb : D.C.Sub A.ch r, IsFrSub D Sb hj := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k r D hj hty α hα
  choose u hu using fun a => exists_up (Dw := Dw) (x := A.ch.χ a ≫ π) fun σ i => ((A.frame a).1 σ i).1
  let Mx : ∀ a, Matrix (Fin (D.C.n (α a))) (Fin (r + 1)) (A.ch.R a) := fun a j i =>
    crd (D.b (α a)) (A.ch.χ a) (hα a) (u a σ ⟨k + i, by omega⟩) j
  have key : ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ i : Fin (r + 1), (fun j => φ (Mx a j i)) = crd (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a S _ φ z e h w hw i
    have e' : spMap φ ≫ A.ch.χ a ≫ π = z ≫ π := by rw [← Category.assoc, e]
    have hw' : w = fun σ i => tanPull φ e' (u a σ i) := up_injective (by rw [hw, up_tanPull, hu])
    subst hw'
    funext j
    exact (basAt_repr (D.b (α a)) φ (A.ch.χ a) (hα a) e h e' _ _).symm
  have mul : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K) (z : Sp K ⟶ X), spMap φ ≫ A.ch.χ a = z →
      ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (w : TVecs Dw M.t (z ≫ π)), up w = (A.fr a).bc φ →
      ∀ cf : Fin (r + 1) → K, ((Mx a).map φ).mulVec cf =
        ∑ i, cf i • crdL (D.b (α a)) z h (w σ ⟨k + i, by omega⟩) := by
    intro a K _ φ z e h w hw cf
    funext j
    simp only [crdL_apply, ← key a K φ z e h w hw, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨⟨α, hα, Mx, fun a K _ φ => ?_, fun a a' K _ φ φ' z e e' h h' => ?_⟩, key⟩
  · have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := fun x _ => hα a (Set.mem_univ (spMap φ x))
    obtain ⟨w, hw⟩ := A.exists_up_fr (φ := φ) rfl
    have hf := A.isFrame_bc (φ := φ) rfl
    have hF := A.flagAt_fr (φ := φ) rfl
    rw [← hw] at hf hF
    refine (injective_iff_map_eq_zero ((Mx a).map φ).mulVecLin).2 fun cf hc => ?_
    refine eq_zero_of_sum (crdL (D.b (α a)) _ h) hj ((isFrame_up_iff _ _).1 hf σ).1
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).1 hv) cf ?_
    rw [← mul a K φ _ rfl h w hw]
    exact hc
  · obtain ⟨w, hw⟩ := A.exists_up_fr e
    obtain ⟨w', hw'⟩ := A.exists_up_fr e'
    have hf := A.isFrame_bc e
    have hF := A.flagAt_fr e
    have hf' := A.isFrame_bc e'
    have hF' := A.flagAt_fr e'
    rw [← hw] at hf hF
    rw [← hw'] at hf' hF'
    have hs : initSpan K (w' σ) (k + r + 1) = initSpan K (w σ) (k + r + 1) := by
      rcases hty with hty | hty
      · exact hF'.initSpan_eq hF σ hty
      · rw [← A.alg_eq e e'] at hf'
        rw [hty, initSpan_full, initSpan_full, ((isFrame_up_iff _ _).1 hf σ).2, ((isFrame_up_iff _ _).1 hf' σ).2]
    have hm : ∀ i : Fin (r + 1), w' σ ⟨k + i, by omega⟩ ∈ initSpan K (w σ) (k + r + 1) := fun i =>
      hs ▸ Submodule.subset_span ⟨_, by show k + (i : ℕ) < k + r + 1; omega, rfl⟩
    choose cf hcf using fun i => exists_sum (crdL (D.b (α a)) z h) hj
      (fun v hv => (crdL_eq_zero_iff D _ _ h hF v).2 hv) (hm i)
    refine ⟨Matrix.of fun p i => cf i p, ?_⟩
    ext j i
    have h1 := D.coord (α a) (α a') K z h h' (w' σ ⟨k + i, by omega⟩)
    rw [← key a' K φ' z e' h' w' hw' i, ← crdL_apply, ← hcf i, ← mul a K φ z e h w hw] at h1
    exact congrFun h1 j

end GlobalTheory.DRFlag.FrSub
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_next_step_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ), (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → ∀ α : A.ch.ι → D.C.A, (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ Sb : D.C.Sub A.ch r, IsFrSub D Sb hj := by
  atlas_forward_decl GlobalTheory.DRFlag.FrSub.exists_isFrSub
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepAtlas

section Lin

variable {R R' N N' : Type} [CommRing R] [CommRing R'] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R' N']
  {m k r : ℕ}

def blk (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) : Fin m → N := fun i =>
  if h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1 then ∑ l : Fin (r + 1), P l ⟨i - k, by omega⟩ • u ⟨k + l, by omega⟩ else u i

theorem blk_add (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) (i : Fin (r + 1)) :
    blk hj P u ⟨k + i, by omega⟩ = ∑ l : Fin (r + 1), P l i • u ⟨k + l, by omega⟩ := by
  have h : k ≤ k + (i : ℕ) ∧ k + (i : ℕ) < k + r + 1 := by omega
  simp only [blk, dif_pos h, Nat.add_sub_cancel_left]

theorem map_blk (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) {φ : R →+* R'}
    (g : N →ₛₗ[φ] N') (i : Fin m) : g (blk hj P u i) = blk hj (P.map φ) (fun j => g (u j)) i := by
  unfold blk
  split_ifs
  · simp only [map_sum, map_smulₛₗ, Matrix.map_apply]
  · rfl

theorem blk_blk (hj : k + r + 1 ≤ m) (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) :
    blk hj Q (blk hj P u) = blk hj (P * Q) u := by
  funext i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    conv_rhs => rw [blk, dif_pos h]
    simp only [blk_add, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · simp only [blk, dif_neg h]

theorem blk_one (hj : k + r + 1 ≤ m) (u : Fin m → N) : blk hj (1 : Matrix _ _ R) u = u := by
  funext i
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    ext
    simp only
    omega
  · simp only [blk, dif_neg h]

theorem initSpan_blk_le (hj : k + r + 1 ≤ m) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (u : Fin m → N) {e : ℕ}
    (he : e ≤ k ∨ k + r + 1 ≤ e) : initSpan R (blk hj P u) e ≤ initSpan R u e := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  have hi' : (i : ℕ) < e := hi
  by_cases h : k ≤ (i : ℕ) ∧ (i : ℕ) < k + r + 1
  · rw [blk, dif_pos h]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    show k + (l : ℕ) < e
    omega
  · rw [blk, dif_neg h]
    exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem initSpan_top (u : Fin m → N) : initSpan R u m = Submodule.span R (Set.range u) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

theorem initSpan_blk (hj : k + r + 1 ≤ m) {P : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (hP : IsUnit P) (u : Fin m → N)
    {e : ℕ} (he : e ≤ k ∨ k + r + 1 ≤ e) : initSpan R (blk hj P u) e = initSpan R u e := by
  obtain ⟨P, rfl⟩ := hP
  refine le_antisymm (initSpan_blk_le hj _ u he) ?_
  have := initSpan_blk_le hj (P⁻¹).val (blk hj P.val u) he
  rwa [blk_blk, Units.mul_inv, blk_one] at this

theorem linearIndependent_blk (hj : k + r + 1 ≤ m) {P : Matrix (Fin (r + 1)) (Fin (r + 1)) R} (hP : IsUnit P)
    {u : Fin m → N} (hu : LinearIndependent R u) : LinearIndependent R (blk hj P u) := by
  obtain ⟨P, rfl⟩ := hP
  have key : ∀ {N : Type} [AddCommGroup N] [Module R N] (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (v : Fin m → N),
      Fintype.linearCombination R v ∘ blk hj Q (Pi.basisFun R (Fin m)) = blk hj Q v := fun Q v => by
    funext i
    rw [Function.comp_apply, map_blk]
    simp [Fintype.linearCombination_apply_single]
  have h1 : LinearIndependent R (blk hj P.val (Pi.basisFun R (Fin m))) := by
    refine LinearIndependent.of_comp (Fintype.linearCombination R (blk hj (P⁻¹).val (Pi.basisFun R (Fin m)))) ?_
    rw [key, blk_blk, Units.inv_mul, blk_one]
    exact (Pi.basisFun R (Fin m)).linearIndependent
  rw [← key]
  exact h1.map' _ (LinearMap.ker_eq_bot'.2 fun a ha => funext (Fintype.linearIndependent_iff.1 hu a ha))

theorem not_mem_initSpan [Nontrivial R] {u : Fin m → N} (hu : LinearIndependent R u) (i : Fin m) :
    u i ∉ initSpan R u i := hu.notMem_span_image (lt_irrefl (i : ℕ))

theorem initSpan_succ_le {u : Fin m → N} {W : Submodule R N} (i : Fin m) (h : initSpan R u i ≤ W) (hi : u i ∈ W) :
    initSpan R u (i + 1) ≤ W := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | h'
  · exact h (Submodule.subset_span ⟨j, h', rfl⟩)
  · rwa [Fin.ext h']

theorem exists_sub_mem (hj : k + r + 1 ≤ m) (u : Fin m → N) {w : N} (hw : w ∈ initSpan R u (k + r + 1)) :
    ∃ v : Fin (r + 1) → R, w - ∑ l : Fin (r + 1), v l • u ⟨k + l, by omega⟩ ∈ initSpan R u k := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj', rfl⟩ := hx
    have hj'' : (j : ℕ) < k + r + 1 := hj'
    by_cases h : (j : ℕ) < k
    · have : u j ∈ initSpan R u k := Submodule.subset_span ⟨j, h, rfl⟩
      exact ⟨0, by simpa using this⟩
    · refine ⟨Pi.single ⟨j - k, by omega⟩ 1, ?_⟩
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have : (⟨k + (j - k), by omega⟩ : Fin m) = j := Fin.ext (by simp only; omega)
      rw [this, sub_self]
      exact Submodule.zero_mem _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert Submodule.add_mem _ ha hb using 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  | smul s x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨s • a, ?_⟩
    convert Submodule.smul_mem _ s ha using 1
    simp only [Pi.smul_apply, smul_eq_mul, smul_sub, Finset.smul_sum, smul_smul]

theorem mem_initSpan_inl {n : ℕ} (b : Module.Basis (Fin k ⊕ Fin n) R N) (v : N) :
    v ∈ initSpan R (fun i : Fin k => b (.inl i)) k ↔ ∀ j, b.repr v (.inr j) = 0 := by
  rw [initSpan_top, show Set.range (fun i : Fin k => b (.inl i)) = b '' Set.range Sum.inl from by
    rw [← Set.range_comp]; rfl, b.mem_span_image]
  refine ⟨fun h j => ?_, fun h => ?_⟩
  · by_contra h'
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.2 h')
    cases hi
  · rintro (i | j) hi
    · exact ⟨i, rfl⟩
    · exact absurd (h j) (Finsupp.mem_support_iff.1 hi)

end Lin

section Carry

variable {Z Z' : Scheme.{0}} {C : Coc Z} {f : Z' ⟶ Z} {L : C.Line f} {S : Type} [CommRing S] {w : Sp S ⟶ Z'}

theorem carries_smul {α : C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α} {ξ : Fin (C.n α) → S} (hξ : L.Carries w α h ξ) (s : Sˣ) :
    L.Carries w α h ((s : S) • ξ) := fun β hw => by
  obtain ⟨u, hu⟩ := hξ β hw
  refine ⟨s * u, ?_⟩
  rw [Matrix.mulVec_smul, hu]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_assoc]

theorem carries_tr {α β : C.A} {hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α} (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) {ξ : Fin (C.n β) → S}
    (hξ : L.Carries w α hα ((C.tr α β (w ≫ f) hα hβ).mulVec ξ)) : L.Carries w β hβ ξ := fun γ hw => by
  obtain ⟨u, hu⟩ := hξ γ hw
  rw [Matrix.mulVec_mulVec, Coc.tr_mul] at hu
  exact ⟨u, hu⟩

theorem exists_chart [IsLocalRing S] (L : C.Line f) (w : Sp S ⟶ Z') : ∃ β, ⊤ ≤ w ⁻¹ᵁ L.B β :=
  FlagMod.exists_chart_of_isLocalRing (eq_top_iff.2 fun x _ => by
    obtain ⟨β, hβ⟩ := L.cover x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨β, hβ⟩) w

end Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}
  {A : Atlas M π ty} {σ : E →+* ℂ} {k r : ℕ} {K : Type} [Field K]

theorem bc_bc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw M.t R) :
    (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  rw [Vecs.bc, Vecs.bc, Vecs.bc, FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

def crdL {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) : TanM (z ≫ π) M.t.G →ₗ[S] (Fin m → S) :=
  LinearMap.pi fun j => (basAt b z h).coord (.inr j)

theorem crd_eq {m : ℕ} {U : X.Opens} {hU : IsAffineOpen U}
    (b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (h : ⊤ ≤ z ⁻¹ᵁ U) (v : TanM (z ≫ π) M.t.G) : crd b z h v = crdL b z h v := rfl

theorem crdL_eq_zero_iff (D : Adapted A σ k) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u))
    (α : D.C.A) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (v : TanM (z ≫ π) M.t.G) :
    crdL (D.b α) z h v = 0 ↔ v ∈ initSpan K (u σ) k := by
  rw [D.int α K z h u hu k le_rfl, mem_initSpan_inl]
  exact funext_iff

theorem linearIndependent_of_flagAt {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)} (hu : A.FlagAt z (up u)) (τ : E →+* ℂ) :
    LinearIndependent K (u τ) := by
  obtain ⟨a, φ, -, hf, -⟩ := hu
  exact ((isFrame_up_iff _ _).1 hf τ).1

def Good (D : Adapted A σ k) (hk : k < Dw.mult σ) {X' : Scheme.{0}} {f : X' ⟶ X} (L : D.C.Line f) (w : Sp K ⟶ X')
    (u : TVecs Dw M.t ((w ≫ f) ≫ π)) : Prop :=
  A.FlagAt (w ≫ f) (up u) ∧ ∀ α h, L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))

variable {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f} {w : Sp K ⟶ X'}
  {u u' : TVecs Dw M.t ((w ≫ f) ≫ π)} {ty' : (E →+* ℂ) → Finset ℕ}

theorem good_of_one (hu : A.FlagAt (w ≫ f) (up u)) {α : D.C.A} {h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ D.C.B α}
    (hc : L.Carries w α h (crd (D.b α) (w ≫ f) h (u σ ⟨k, hk⟩))) : Good D hk L w u :=
  ⟨hu, fun β hβ => carries_tr (hα := h) hβ (by rwa [D.coord])⟩

theorem Good.le (h : Good D hk L w u) (h' : Good D hk L w u') (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j := by
  intro τ j hj
  by_cases hτ : τ = σ
  swap
  · exact (h'.1.initSpan_eq h.1 τ (h2 τ hτ ▸ hj)).le
  subst hτ
  rw [h1, Finset.mem_insert] at hj
  rcases hj with rfl | hj
  swap
  · exact (h'.1.initSpan_eq h.1 τ hj).le
  obtain ⟨β, hβ⟩ := exists_chart L w
  have hα := le_preimage_map f (L.le β) hβ
  obtain ⟨s, hs⟩ := h.2 _ hα β hβ
  obtain ⟨s', hs'⟩ := h'.2 _ hα β hβ
  rw [Coc.tr_self, Matrix.one_mulVec, crd_eq] at hs hs'
  have hle := FlagMod.initSpan_mono (R := K) (u τ) (Nat.le_succ k)
  refine initSpan_succ_le ⟨k, hk⟩ (fun v hv => hle ?_) ?_
  · exact (crdL_eq_zero_iff D h.1 _ hα v).1 ((crdL_eq_zero_iff D h'.1 _ hα v).2 hv)
  · have : u' τ ⟨k, hk⟩ - ((s' * s⁻¹ : Kˣ) : K) • u τ ⟨k, hk⟩ ∈ initSpan K (u τ) k := by
      rw [← crdL_eq_zero_iff D h.1 _ hα, map_sub, map_smul, hs, hs']
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, Pi.zero_apply, mul_assoc,
        Units.inv_mul_cancel_left, sub_self]
    have h3 : u τ ⟨k, hk⟩ ∈ initSpan K (u τ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
    simpa using Submodule.add_mem _ (hle this) (Submodule.smul_mem _ ((s' * s⁻¹ : Kˣ) : K) h3)

theorem Good.of_le (h : Good D hk L w u) {a : A.ch.ι} {φ : A.ch.R a →+* K} (e : spMap φ ≫ A.ch.χ a = w ≫ f)
    (hf : LocM.IsFrame M.t (φ.comp (A.alg a)) ((w ≫ f) ≫ π) (up u')) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (hle : ∀ τ, ∀ j ∈ ty' τ, initSpan K (u' τ) j ≤ initSpan K (u τ) j) :
    Good D hk L w u' := by
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have hsub : ∀ τ, ∀ j ∈ ty τ, j ∈ ty' τ := fun τ j hj => by
    by_cases hτ : τ = σ
    · subst hτ
      rw [h1]
      exact Finset.mem_insert_of_mem hj
    · rwa [h2 τ hτ]
  have hi := linearIndependent_of_flagAt h.1
  have hF : A.FlagAt (w ≫ f) (up u') := (A.flagAt_iff e h₀ u').2 ⟨hf, fun τ j hj =>
    (initSpan_eq_of_le (hi τ) ((isFrame_up_iff _ _).1 hf τ).1 (hle τ j (hsub τ j hj))).trans
      (((A.flagAt_iff e h₀ u).1 h.1).2 τ j hj)⟩
  refine ⟨hF, fun α hα => ?_⟩
  have h3 : u' σ ⟨k, hk⟩ ∈ initSpan K (u' σ) (k + 1) := Submodule.subset_span ⟨_, Nat.lt_succ_self k, rfl⟩
  obtain ⟨s, hs, -⟩ := FlagMod.existsUnique_sub_mem_initSpan (hi σ) ⟨k, hk⟩
    (hle σ (k + 1) (h1 ▸ Finset.mem_insert_self _ _) h3)
  have hs' := (crdL_eq_zero_iff D h.1 α hα _).2 hs
  rw [map_sub, map_smul, sub_eq_zero] at hs'
  have h0 : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, crdL_eq_zero_iff D hF] at hs'
    exact not_mem_initSpan (linearIndependent_of_flagAt hF σ) ⟨k, hk⟩ hs'
  rw [crd_eq, hs']
  exact carries_smul (h.2 α hα) (Units.mk0 s h0)

open Classical in

def chg (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) : TVecs Dw M.t x := Function.update u σ (blk hj P (u σ))

theorem chg_self (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) : chg hj P u σ = blk hj P (u σ) := by
  classical
  unfold chg
  convert Function.update_self σ _ u

theorem chg_ne (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S)
    {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) {τ : E →+* ℂ} (h : τ ≠ σ) : chg hj P u τ = u τ := by
  classical
  unfold chg
  convert Function.update_of_ne h _ u

theorem isFrame_chg (hj : k + r + 1 ≤ Dw.mult σ) {S : Type} [CommRing S] {P : Matrix (Fin (r + 1)) (Fin (r + 1)) S}
    (hP : IsUnit P) {x : Sp S ⟶ M.X} {u : TVecs Dw M.t x} {g : c.F →+* S} (hu : LocM.IsFrame M.t g x (up u)) :
    LocM.IsFrame M.t g x (up (chg hj P u)) := by
  rw [isFrame_up_iff] at hu ⊢
  intro τ
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, ← initSpan_top, initSpan_blk hj hP _ (Or.inr hj), initSpan_top]
    exact ⟨linearIndependent_blk hj hP (hu τ).1, (hu τ).2⟩
  · rw [chg_ne hj P u hτ]
    exact hu τ

theorem tanPull_chg (hj : k + r + 1 ≤ Dw.mult σ) {S S' : Type} [CommRing S] [CommRing S']
    (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S) (φ : S →+* S') {x : Sp S ⟶ M.X} {x' : Sp S' ⟶ M.X}
    (e : spMap φ ≫ x = x') (u : TVecs Dw M.t x) :
    (fun τ i => tanPull φ e (chg hj P u τ i)) = chg hj (P.map φ) (fun τ i => tanPull φ e (u τ i)) := by
  funext τ i
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, chg_self, map_blk]
  · rw [chg_ne hj _ _ hτ, chg_ne hj _ _ hτ]

theorem flagAt_chg (hj : k + r + 1 ≤ Dw.mult σ) (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e)
    {P : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hP : IsUnit P) {z : Sp K ⟶ X} {u : TVecs Dw M.t (z ≫ π)}
    (hu : A.FlagAt z (up u)) : A.FlagAt z (up (chg hj P u)) := by
  obtain ⟨a, φ, e, -⟩ := id hu
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨h1, h2⟩ := (A.flagAt_iff e h₀ u).1 hu
  refine (A.flagAt_iff e h₀ _).2 ⟨isFrame_chg hj hP h1, fun τ j hj' => Eq.trans ?_ (h2 τ j hj')⟩
  by_cases hτ : τ = σ
  · subst hτ
    rw [chg_self, initSpan_blk hj hP _ (hty j hj')]
  · rw [chg_ne hj _ _ hτ]

theorem crdL_sum {Sb : D.C.Sub A.ch r} {hj : k + r + 1 ≤ Dw.mult σ} (hS : IsFrSub D Sb hj) {a : A.ch.ι}
    {φ : A.ch.R a →+* K} {z : Sp K ⟶ X} (e : spMap φ ≫ A.ch.χ a = z) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (Sb.α a))
    {u : TVecs Dw M.t (z ≫ π)} (hu : up u = (A.fr a).bc φ) (v : Fin (r + 1) → K) :
    crdL (D.b (Sb.α a)) z h (∑ i : Fin (r + 1), v i • u σ ⟨k + i, by omega⟩) = ((Sb.M a).map φ).mulVec v := by
  rw [map_sum]
  simp only [map_smul, ← crd_eq, ← hS a K φ z e h u hu]
  funext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_vec {Sb : D.C.Sub A.ch r} {hj : k + r + 1 ≤ Dw.mult σ} (hS : IsFrSub D Sb hj)
    (hty : k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) (hk : k < Dw.mult σ) {a : A.ch.ι}
    {φ : A.ch.R a →+* K} {u : Vecs Dw M.t K} (hu : A.FlagAt (spMap φ ≫ A.ch.χ a) u) :
    ∃ v : Fin (r + 1) → K, v ≠ 0 ∧ ∀ z : Sp K ⟶ X, z = spMap φ ≫ A.ch.χ a → ∀ U : TVecs Dw M.t (z ≫ π), up U = u →
      ∀ h, crd (D.b (Sb.α a)) z h (U σ ⟨k, hk⟩) = ((Sb.M a).map φ).mulVec v := by
  obtain ⟨U, rfl⟩ := hu.exists_up
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr (φ := φ) rfl
  obtain ⟨h1, h2⟩ := (A.flagAt_iff rfl h₀ U).1 hu
  have hF : A.FlagAt (spMap φ ≫ A.ch.χ a) (up u₀) := h₀ ▸ A.flagAt_fr rfl
  have h3 : U σ ⟨k, hk⟩ ∈ initSpan K (u₀ σ) (k + r + 1) := by
    have h4 : U σ ⟨k, hk⟩ ∈ initSpan K (U σ) (k + r + 1) := Submodule.subset_span ⟨_, show k < k + r + 1 by omega, rfl⟩
    rcases hty with h | h
    · rwa [← h2 σ _ h]
    · have f₀ := A.isFrame_bc (φ := φ) rfl
      rw [← h₀] at f₀
      rw [h, initSpan_top, ((isFrame_up_iff _ _).1 f₀ σ).2, ← ((isFrame_up_iff _ _).1 h1 σ).2]
      exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_sub_mem hj _ h3
  have key : ∀ h, crd (D.b (Sb.α a)) _ h (U σ ⟨k, hk⟩) = ((Sb.M a).map φ).mulVec v := fun h => by
    have := (crdL_eq_zero_iff D hF _ h _).2 hv
    rwa [map_sub, sub_eq_zero, crdL_sum hS rfl h h₀] at this
  refine ⟨v, ?_, ?_⟩
  · rintro rfl
    have := key (le_preimage_comp _ (Sb.le a))
    rw [Matrix.mulVec_zero, crd_eq, crdL_eq_zero_iff D hu] at this
    exact not_mem_initSpan (linearIndependent_of_flagAt hu σ) ⟨k, hk⟩ this
  · rintro z rfl U' hU'
    rw [up_injective hU']
    exact key

section Closure

variable {D : Adapted A σ k} {Sb : D.C.Sub A.ch r} (Cl : Sb.Closure (π ≫ M.s))

def frBelow (q : Cl.ch'.ι) : TVecs Dw M.t ((Cl.ch'.χ q ≫ Cl.f) ≫ π) := (A.exists_up_fr (Cl.sq q).symm).choose

theorem up_frBelow (q : Cl.ch'.ι) : up (frBelow Cl q) = (A.fr (Cl.b q)).bc (Cl.ρ q) :=
  (A.exists_up_fr (Cl.sq q).symm).choose_spec

def pre (hj : k + r + 1 ≤ Dw.mult σ) : PreAtlas M Cl.Z' where
  ch := Cl.ch'
  alg q := (Cl.ρ q).comp (A.alg (Cl.b q))
  fr q := up (chg hj (Cl.P q) (frBelow Cl q))

theorem chg_k (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) {S : Type} [CommRing S]
    (P : Matrix (Fin (r + 1)) (Fin (r + 1)) S) {x : Sp S ⟶ M.X} (u : TVecs Dw M.t x) :
    chg hj P u σ ⟨k, hk⟩ = ∑ l : Fin (r + 1), P l 0 • u σ ⟨k + l, by omega⟩ := by
  rw [chg_self]
  exact blk_add hj P _ 0

theorem sq_point (q : Cl.ch'.ι) {ψ : Cl.ch'.R q →+* K} {w : Sp K ⟶ Cl.Z'} (e : spMap ψ ≫ Cl.ch'.χ q = w) :
    spMap (ψ.comp (Cl.ρ q)) ≫ A.ch.χ (Cl.b q) = w ≫ Cl.f := by
  rw [← spMap_comp', Category.assoc, ← Cl.sq, ← Category.assoc, e]

theorem exists_good (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (q : Cl.ch'.ι) {ψ : Cl.ch'.R q →+* K} {w : Sp K ⟶ Cl.Z'}
    (e : spMap ψ ≫ Cl.ch'.χ q = w) : ∃ U : TVecs Dw M.t ((w ≫ Cl.f) ≫ π),
      up U = ((pre Cl hj).fr q).bc ψ ∧ Good D hk Cl.L w U := by
  have e' := sq_point Cl q e
  have e2 : spMap ψ ≫ (Cl.ch'.χ q ≫ Cl.f) ≫ π = (w ≫ Cl.f) ≫ π := by
    rw [← e]; simp only [Category.assoc]
  let U₀ : TVecs Dw M.t ((w ≫ Cl.f) ≫ π) := fun τ i => tanPull ψ e2 (frBelow Cl q τ i)
  have h₀ : up U₀ = (A.fr (Cl.b q)).bc (ψ.comp (Cl.ρ q)) := by
    rw [up_tanPull ψ e2, up_frBelow, bc_bc]
  have hF : A.FlagAt (w ≫ Cl.f) (up U₀) := h₀ ▸ A.flagAt_fr e'
  have hP : IsUnit ((Cl.P q).map ψ) := by
    have := (Cl.P_unit q).map (RingHom.mapMatrix ψ)
    exact this
  have hU : (fun τ i => tanPull ψ e2 (chg hj (Cl.P q) (frBelow Cl q) τ i)) = chg hj ((Cl.P q).map ψ) U₀ :=
    tanPull_chg hj _ ψ e2 _
  refine ⟨chg hj ((Cl.P q).map ψ) U₀, ?_, ?_⟩
  · rw [← hU]
    exact up_tanPull ψ e2 _
  · have h : ⊤ ≤ (w ≫ Cl.f) ⁻¹ᵁ D.C.B (Sb.α (Cl.b q)) := e' ▸ le_preimage_comp _ (Sb.le _)
    refine good_of_one (flagAt_chg hj hty hP hF) (α := Sb.α (Cl.b q)) (h := h) ?_
    rw [crd_eq, chg_k hj hk]
    have := crdL_sum hS e' h h₀ (fun l => ψ (Cl.P q l 0))
    simp only [Matrix.map_apply]
    rw [this]
    exact Cl.car q K ψ w e h

theorem pre_flagAt_iff (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (w : Sp K ⟶ Cl.Z') (U : TVecs Dw M.t ((w ≫ Cl.f) ≫ π)) :
    (pre Cl hj).FlagAt (Cl.f ≫ π) ty' w (up U) ↔ Good D hk Cl.L w U := by
  have ex : w ≫ Cl.f ≫ π = (w ≫ Cl.f) ≫ π := (Category.assoc _ _ _).symm
  constructor
  · rintro ⟨q, ψ, e, hf, hs⟩
    obtain ⟨U₀, hU₀, hg⟩ := exists_good Cl hj hk hS hty q e
    rw [ex] at hf hs
    have hs' : SameFlag ty' M.t ((w ≫ Cl.f) ≫ π) (up U₀) (up U) := by rw [hU₀]; exact hs
    rw [sameFlag_up_iff] at hs'
    exact hg.of_le (sq_point Cl q e) hf h1 h2 hs'
  · intro hg
    obtain ⟨a, φ, e, -⟩ := id hg.1
    have hr : w (IsLocalRing.closedPoint K) ∈ Cl.ch'.carrier := by
      rw [Cl.carrier_eq]
      exact A.ch.range_subset e ⟨IsLocalRing.closedPoint K, rfl⟩
    obtain ⟨q, ψ, eq⟩ := Cl.ch'.exists_fac w hr
    obtain ⟨U₀, hU₀, hg₀⟩ := exists_good Cl hj hk hS hty q eq
    have e' := sq_point Cl q eq
    obtain ⟨u₁, h₁⟩ := A.exists_up_fr e'
    have hfr := ((A.flagAt_iff e' h₁ U).1 hg.1).1
    have hs := (sameFlag_up_iff U₀ U).2 (hg₀.le hg h1 h2)
    rw [hU₀] at hs
    exact ⟨q, ψ, eq, by rw [ex]; exact hfr, by rw [ex]; exact hs⟩

theorem pre_cover : Cl.ch'.carrier = (Cl.f ≫ π) ⁻¹' Set.range M.j := by
  rw [Cl.carrier_eq, A.cover]
  ext x
  simp only [Set.mem_preimage, Scheme.Hom.comp_apply]

theorem pre_alg_s (q : Cl.ch'.ι) : Cl.ch'.χ q ≫ (Cl.f ≫ π) ≫ M.s =
    spMap (((Cl.ρ q).comp (A.alg (Cl.b q))).comp V.subtype) := by
  have := A.affineOpenChart_comp_structure_eq_spMap (Cl.sq q).symm
  simp only [Category.assoc] at this ⊢
  exact this

theorem pre_smooth (q : Cl.ch'.ι) : Smooth (Cl.ch'.χ q ≫ Cl.f ≫ π) := by
  have h3 : Cl.ch'.χ q ≫ Cl.f ≫ π = spMap (Cl.ρ q) ≫ A.ch.χ (Cl.b q) ≫ π := by
    rw [← Category.assoc, Cl.sq, Category.assoc]
  have := Cl.smooth q
  have := A.smooth (Cl.b q)
  rw [h3]
  infer_instance

theorem pre_frame (hj : k + r + 1 ≤ Dw.mult σ) (q : Cl.ch'.ι) : LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q)))
    (Cl.ch'.χ q ≫ Cl.f ≫ π) (up (chg hj (Cl.P q) (frBelow Cl q))) := by
  have hf := A.isFrame_bc (Cl.sq q).symm
  have hf' : LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) ((Cl.ch'.χ q ≫ Cl.f) ≫ π) (up (frBelow Cl q)) := by
    rw [up_frBelow]; exact hf
  have h5 : ∀ {x x' : Sp (Cl.ch'.R q) ⟶ M.X} (_ : x = x') {v : Vecs Dw M.t (Cl.ch'.R q)},
      LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) x v → LocM.IsFrame M.t ((Cl.ρ q).comp (A.alg (Cl.b q))) x' v := by
    rintro _ _ rfl _ h
    exact h
  exact h5 (Category.assoc _ _ _) (isFrame_chg hj (Cl.P_unit q) hf')

theorem pre_glue (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) (h1 : ty' σ = insert (k + 1) (ty σ))
    (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') (K : Type) [Field K] (q q' : Cl.ch'.ι) (ψ : Cl.ch'.R q →+* K)
    (ψ' : Cl.ch'.R q' →+* K) (e : spMap ψ ≫ Cl.ch'.χ q = spMap ψ' ≫ Cl.ch'.χ q') :
    SameFlag ty' M.t (spMap ψ ≫ Cl.ch'.χ q ≫ Cl.f ≫ π) (((pre Cl hj).fr q).bc ψ) (((pre Cl hj).fr q').bc ψ') := by
  obtain ⟨U, hU, hg⟩ := exists_good Cl hj hk hS hty q (rfl : spMap ψ ≫ Cl.ch'.χ q = _)
  obtain ⟨U', hU', hg'⟩ := exists_good Cl hj hk hS hty q' e.symm
  have hs := (sameFlag_up_iff U U').2 (hg.le hg' h1 h2)
  rw [hU, hU'] at hs
  have ex : spMap ψ ≫ Cl.ch'.χ q ≫ Cl.f ≫ π = ((spMap ψ ≫ Cl.ch'.χ q) ≫ Cl.f) ≫ π := by
    simp only [Category.assoc]
  rw [ex]
  exact hs

def atlas (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (hS : IsFrSub D Sb hj)
    (hty₀ : k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) (hty : ∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e)
    (h1 : ty' σ = insert (k + 1) (ty σ)) (h2 : ∀ σ', σ' ≠ σ → ty' σ' = ty σ') : Atlas M (Cl.f ≫ π) ty' where
  toPreAtlas := pre Cl hj
  cover := pre_cover Cl
  alg_s q := pre_alg_s Cl q
  smooth q := pre_smooth Cl q
  frame q := pre_frame Cl hj q
  glue K _ q q' ψ ψ' e := pre_glue Cl hj hk hS hty h1 h2 K q q' ψ ψ' e
  bij K _ g y hy u hu := by
    obtain ⟨w₀, ⟨hw₀, hF⟩, hun⟩ := A.bij K g y hy u hu
    obtain ⟨a, φ, rfl, -⟩ := id hF
    obtain ⟨v, hv0, hv⟩ := exists_vec hS hty₀ hk hF
    obtain ⟨w, ⟨hw1, hw2⟩, hwu⟩ := Cl.bij a K φ v hv0
    have hx : ∀ {w' : Sp K ⟶ Cl.Z'}, w' ≫ Cl.f ≫ π = y ≫ M.j → ∃ U : TVecs Dw M.t ((w' ≫ Cl.f) ≫ π), up U = u :=
      fun {w'} e => exists_up fun τ i => by
        have e' : (w' ≫ Cl.f) ≫ π = y ≫ M.j := (Category.assoc _ _ _).trans e
        rw [e']
        exact (hu.1 τ i).1
    have hw : w ≫ Cl.f ≫ π = y ≫ M.j := by rw [← Category.assoc, hw1, hw₀]
    refine ⟨w, ⟨hw, ?_⟩, ?_⟩
    · have h3 : A.FlagAt (w ≫ Cl.f) u := by rw [hw1]; exact hF
      have h : ⊤ ≤ (w ≫ Cl.f) ⁻¹ᵁ D.C.B (Sb.α a) := by rw [hw1]; exact le_preimage_comp _ (Sb.le a)
      obtain ⟨U, rfl⟩ := hx hw
      refine (pre_flagAt_iff Cl hj hk hS hty h1 h2 w U).2 (good_of_one h3 (α := Sb.α a) (h := h) ?_)
      rw [hv _ hw1 U rfl h]
      exact hw2 h
    · rintro w' ⟨e1, e2⟩
      obtain ⟨U, rfl⟩ := hx e1
      have hg := (pre_flagAt_iff Cl hj hk hS hty h1 h2 w' U).1 e2
      have e3 : w' ≫ Cl.f = spMap φ ≫ A.ch.χ a :=
        hun _ ⟨(Category.assoc _ _ _).trans e1, hg.1⟩
      refine hwu w' ⟨e3, fun h => ?_⟩
      rw [← hv _ e3 U rfl h]
      exact hg.2 _ h

end Closure

theorem exists_stepAtlas (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F)
    [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k)
    (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ M.s))
    (ty' : (E →+* ℂ) → Finset ℕ) : IsFrSub D Sb hj → (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) →
      (∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) → ty' σ = insert (k + 1) (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') →
      ∃ A' : Atlas M (Cl.f ≫ π) ty', StepRel D hk Cl.L A' := fun hS hty₀ hty h1 h2 =>
  ⟨atlas Cl hj hk hS hty₀ hty h1 h2, fun _ _ w U => pre_flagAt_iff Cl hj hk hS hty h1 h2 w U⟩

end GlobalTheory.DRFlag.StepAtlas
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_substep_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ M.s)) (ty' : (E →+* ℂ) → Finset ℕ), IsFrSub D Sb hj → (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → (∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) → ty' σ = insert (k + 1) (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') → ∃ A' : Atlas M (Cl.f ≫ π) ty', StepRel D hk Cl.L A' := by
  atlas_forward_decl GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepInt

def optionSumEquiv (A B : Type) : Option A ⊕ B ≃ A ⊕ Option B where
  toFun
    | .inl none => .inr none
    | .inl (some a) => .inl a
    | .inr b => .inr (some b)
  invFun
    | .inl a => .inl (some a)
    | .inr none => .inl none
    | .inr (some b) => .inr b
  left_inv := by rintro ((_ | a) | b) <;> rfl
  right_inv := by rintro (a | (_ | b)) <;> rfl

theorem exists_basis_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (c : Fin n) (hc : IsUnit (η c)) :
    ∃ (m : ℕ) (b' : Module.Basis (Fin (k + 1) ⊕ Fin m) R N), (∀ i : Fin k, b' (.inl i.castSucc) = b (.inl i)) ∧
      b' (.inl (Fin.last k)) = ∑ j, η j • b (.inr j) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.pos; omega⟩
  have hr : b.repr (∑ j, η j • b (.inr j)) (.inr c) = η c := by
    simp [Finsupp.single_apply]
  have hd : IsUnit (b.det (Function.update b (.inr c) (∑ j, η j • b (.inr j)))) := by
    rw [Module.Basis.det_apply, Module.Basis.toMatrix_update, Module.Basis.toMatrix_self, ← Matrix.cramer_apply,
      Matrix.cramer_one]
    rw [← hr] at hc
    exact hc
  obtain ⟨h1, h2⟩ := (Module.Basis.is_basis_iff_det b).2 hd
  let q : Fin (k + 1) ⊕ Fin m ≃ Fin k ⊕ Fin (m + 1) :=
    (Equiv.sumCongr finSuccEquivLast (Equiv.refl _)).trans
      ((optionSumEquiv _ _).trans (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv' c).symm))
  refine ⟨m, (Module.Basis.mk h1 h2.ge).reindex q.symm, fun i => ?_, ?_⟩
  · have : q (.inl i.castSucc) = .inl i := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_of_ne (by simp)]
  · have : q (.inl (Fin.last k)) = .inr c := by simp [q, optionSumEquiv]
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, this, Module.Basis.mk_apply, Function.update_self]

theorem initSpan_castSucc {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {k : ℕ} (v : Fin (k + 1) → N)
    {j : ℕ} (hj : j ≤ k) : initSpan R v j = initSpan R (fun i : Fin k => v i.castSucc) j := by
  unfold initSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    exact ⟨⟨i, by omega⟩, hi', rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

theorem initSpan_succ {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k : ℕ} (v : Fin M → N) (hk : k < M) :
    initSpan R v (k + 1) = initSpan R v k ⊔ Submodule.span R {v ⟨k, hk⟩} := by
  unfold initSpan
  rw [← Submodule.span_union, ← Set.image_singleton, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem initSpan_step {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {M k n : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin n) R N) (η : Fin n → R) (u : Fin M → N) (hk : k < M)
    (hu : ∀ j ≤ k, initSpan R u j = initSpan R (fun i : Fin k => b (.inl i)) j) (e : Rˣ)
    (he : ∀ i, b.repr (u ⟨k, hk⟩) (.inr i) = (e : R) * η i) (v : Fin (k + 1) → N)
    (hv : ∀ i : Fin k, v i.castSucc = b (.inl i)) (hv' : v (Fin.last k) = ∑ j, η j • b (.inr j)) :
    ∀ j ≤ k + 1, initSpan R u j = initSpan R v j := by
  have h0 : ∀ j ≤ k, initSpan R u j = initSpan R v j := fun j hj => by
    rw [initSpan_castSucc v hj, hu j hj]; simp only [hv]
  intro j hj
  rcases hj.eq_or_lt with rfl | hj
  · rw [initSpan_succ u hk, initSpan_succ v (Nat.lt_succ_self k), h0 k le_rfl]
    have hs : ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) ∈ initSpan R v k :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, i.2, hv i⟩)
    have hw : u ⟨k, hk⟩ = ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) +
        (e : R) • v ⟨k, Nat.lt_succ_self k⟩ := by
      conv_lhs => rw [← b.sum_repr (u ⟨k, hk⟩), Fintype.sum_sum_type]
      rw [show v ⟨k, Nat.lt_succ_self k⟩ = _ from hv', Finset.smul_sum]
      simp only [he, mul_smul]
    generalize ∑ i : Fin k, b.repr (u ⟨k, hk⟩) (.inl i) • b (.inl i) = s at hs hw
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Submodule.span_singleton_le_iff_mem, hw]
      exact Submodule.add_mem_sup hs (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · rw [Submodule.span_singleton_le_iff_mem, ← Submodule.smul_mem_iff_of_isUnit _ e.isUnit,
        ← sub_eq_iff_eq_add'.2 hw]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
        (Submodule.mem_sup_left hs)
  · exact h0 j (by omega)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem tanPull_basPull {Y X X' : Scheme.{0}} {t : SAB H Y} {π : X ⟶ Y} {f : X' ⟶ X} {U : X.Opens} {hU : IsAffineOpen U}
    {U' : X'.Opens} {hU' : IsAffineOpen U'} (le : U' ≤ f ⁻¹ᵁ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(X, U) (TanM (tau hU ≫ π) t.G)) {S : Type} [CommRing S] (w : Sp S ⟶ X')
    (hw : ⊤ ≤ w ⁻¹ᵁ U') {x : Sp S ⟶ Y}
    (e₀ : spMap (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) ≫ tau hU ≫ π = tau hU' ≫ f ≫ π)
    (e₁ : spMap (ev w U' hw) ≫ tau hU' ≫ f ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) U (le_preimage_map f le hw)) ≫ tau hU ≫ π = x) (i : κ) :
    tanPull (ev w U' hw) e₁ (basPull _ e₀ b i) = basPull _ e₂ b i := by
  have h1 : spMap (ev w U' hw) ≫ tau hU' ≫ f = w ≫ f := by rw [← Category.assoc, tau, spMap_ev]
  have h2 : (ev w U' hw).comp (ev (tau hU' ≫ f) U (le_preimage_map f le (tau_le hU' le_rfl))) =
      ev (w ≫ f) U (le_preimage_map f le hw) := by
    rw [← ev_spMap _ _ _ _ (h1 ▸ le_preimage_map f le hw)]
    exact FlagMod.ev_congr h1 _ _ _
  rw [basPull_apply, basPull_apply, tanPull_tanPull _ _ _ _ (by rw [h2]; exact e₂)]
  apply tan_ext
  rw [FlagMod.tanPull_left, FlagMod.tanPull_left, h2]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

theorem flag_data {D : Adapted A σ k} {hk : k < Dw.mult σ} {X' : Scheme.{0}} {f : X' ⟶ X} {L : D.C.Line f}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas M (f ≫ π) ty'} (h : StepRel D hk L A') (β : L.J) {K : Type} [Field K]
    (w : Sp K ⟶ X') (hw : ⊤ ≤ w ⁻¹ᵁ L.B β) {x : Sp K ⟶ M.X} (e : (w ≫ f) ≫ π = x)
    (e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = x)
    (u : TVecs Dw M.t x) (hu : A'.FlagAt w (up u)) :
    (∀ j ≤ k, initSpan K (u σ) j = initSpan K (fun i : Fin k => basPull _ e₂ (D.b (L.a β)) (.inl i)) j) ∧
      ∃ e : Kˣ, ∀ i, (basPull _ e₂ (D.b (L.a β))).repr (u σ ⟨k, hk⟩) (.inr i) = (e : K) * ev w _ hw (L.η β i) := by
  subst e
  obtain ⟨h1, h2⟩ := (h K w u).1 hu
  refine ⟨D.int (L.a β) K (w ≫ f) _ u h1, ?_⟩
  obtain ⟨e, he⟩ := h2 (L.a β) (le_preimage_map f (L.le β) hw) β hw
  rw [Coc.tr_self, Matrix.one_mulVec] at he
  exact ⟨e, fun i => congrFun he i⟩

theorem intStep_succ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F)
    [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X)
    (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ)
    (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty')
    (h : StepRel D hk L A') : IntStep A' σ (k + 1) := by
  intro x
  obtain ⟨β, hx⟩ := L.cover x
  obtain ⟨c₀, hc⟩ := L.unit β
  have e₀ : spMap (ev (tau (L.aff β) ≫ f) _ (le_preimage_map f (L.le β) (tau_le (L.aff β) le_rfl))) ≫
      tau (D.C.aff (L.a β)) ≫ π = tau (L.aff β) ≫ f ≫ π := by
    rw [← Category.assoc, tau.eq_1 (D.C.aff (L.a β)), spMap_ev, Category.assoc]
  obtain ⟨m, b', h1, h2⟩ := exists_basis_succ (basPull _ e₀ (D.b (L.a β))) (L.η β) c₀ hc
  refine ⟨L.B β, L.aff β, m, b', hx, fun K _ w hw u hu => ?_⟩
  have e₂ : spMap (ev (w ≫ f) _ (le_preimage_map f (L.le β) hw)) ≫ tau (D.C.aff (L.a β)) ≫ π = w ≫ f ≫ π := by
    rw [← Category.assoc, tau, spMap_ev, Category.assoc]
  obtain ⟨g1, e, g2⟩ := flag_data h β w hw (Category.assoc _ _ _) e₂ u hu
  refine initSpan_step _ _ (u σ) hk g1 e g2 _ (fun i => ?_) ?_
  · rw [basAt, basPull_apply, h1]
    exact tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _
  · rw [basAt, basPull_apply, h2, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulₛₗ, tanPull_basPull (L.le β) _ w hw e₀ _ e₂ _]

end GlobalTheory.DRFlag.StepInt
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_linear_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), StepRel D hk L A' → IntStep A' σ (k + 1) := by
  atlas_forward_decl GlobalTheory.DRFlag.StepInt.intStep_succ
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp
  tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.StepLift

theorem initSpan_map {K N N' : Type} [CommRing K] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] {m : ℕ}
    (L : N →ₗ[K] N') (v : Fin m → N) (j : ℕ) : initSpan K (fun i => L (v i)) j = (initSpan K v j).map L := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

theorem initSpan_of_le {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {m : ℕ}
    (v : Fin m → N) {j : ℕ} (hj : m ≤ j) : initSpan K v j = Submodule.span K (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun i => i.2.trans_le hj

theorem exists_isUnit_repr {R N : Type} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] {k m : ℕ} {κ : Type}
    (b : Module.Basis (Fin k ⊕ Fin m) R N) (c : Module.Basis κ R N) (q : κ)
    (h : ∀ i, c.repr (b (.inl i)) q = 0) : ∃ j, IsUnit (b.repr (c q) (.inr j)) := by
  by_contra! hn
  have h1 : c.repr (c q) q ∈ IsLocalRing.maximalIdeal R := by
    rw [← b.sum_repr (c q), map_sum, Finsupp.finset_sum_apply]
    refine Ideal.sum_mem _ fun x _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rcases x with i | j
    · rw [h i, mul_zero]; exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (hn j)
  rw [c.repr_self, Finsupp.single_eq_same] at h1
  exact h1 isUnit_one

theorem repr_eq_zero_of_mem {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {κ : Type} {d : ℕ}
    (c : Module.Basis κ K N) (e : Fin d ↪ κ) {k : ℕ} (hk : k < d) {v : N}
    (hv : v ∈ initSpan K (fun j => c (e j)) k) : c.repr v (e ⟨k, hk⟩) = 0 := by
  have : initSpan K (fun j => c (e j)) k ≤ LinearMap.ker (c.coord (e ⟨k, hk⟩)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hne : e j ≠ e ⟨k, hk⟩ := fun h => by
      obtain rfl := e.injective h
      exact lt_irrefl k hj
    simp [Finsupp.single_eq_of_ne hne.symm]
  exact this hv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem flagAt_of_initSpan_eq {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
    {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty}
    {K : Type} [Field K] {w : Sp K ⟶ X} {x : Sp K ⟶ M.X} (hx : w ≫ π = x) {u u' : TVecs Dw M.t x}
    (h : A.FlagAt w (up u)) (hli : ∀ σ, LinearIndependent K (u' σ))
    (hs : ∀ σ j, initSpan K (u' σ) j = initSpan K (u σ) j) : A.FlagAt w (up u') := by
  subst hx
  obtain ⟨a, φ, e, -⟩ := id h
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  obtain ⟨hf, hs'⟩ := (A.flagAt_iff e h₀ u).1 h
  refine (A.flagAt_iff e h₀ u').2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨hli σ, ?_⟩, fun σ j hj => (hs σ j).trans (hs' σ j hj)⟩
  rw [← initSpan_of_le _ le_rfl, hs, initSpan_of_le _ le_rfl]
  exact ((isFrame_up_iff _ _).1 hf σ).2

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_int_frame {Z : Mdl Y i₀} (hZ : HasDR Z) {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (φ : R →+* K)
    (z : Sp R ⟶ Z.X) {w : Sp K ⟶ Z.X} (e : spMap φ ≫ z = w) (e' : spMap φ ≫ z ≫ Z.π = w ≫ Z.π)
    (hw : Set.range w ⊆ Z.opn) {u : TVecs Dw (Y Z.i).t (w ≫ Z.π)} (hu : Z.FlagAt w (up u)) :
    ∃ T : TVecs Dw (Y Z.i).t (z ≫ Z.π),
      (∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM (z ≫ Z.π) (Y Z.i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
        ∀ j, c (q j) = T σ j) ∧
      ∀ σ j, initSpan K (fun i => tanPull φ e' (T σ i)) j = initSpan K (u σ) j := by
  obtain ⟨U, hU, fr, hx, h1, h2⟩ := hZ.2 (z (IsLocalRing.closedPoint R))
  have hz : ⊤ ≤ z ⁻¹ᵁ U := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ U)).1 hx).ge
  have ht : ∀ σ j, IsTanAtG (Y Z.i).t (tau hU ≫ Z.π) (fr σ j) := fun σ j => by
    obtain ⟨n, v, q, hq, hv, -⟩ := h1 σ
    rw [← hq]; exact hv _
  have ez : spMap (ev z U hz) ≫ tau hU ≫ Z.π = z ≫ Z.π := by rw [← Category.assoc, tau, spMap_ev]
  refine ⟨fun σ j => tanPull (ev z U hz) ez (tanOf (ht σ j)), fun σ => ?_, fun σ j => ?_⟩
  · obtain ⟨n, v, q, hq, hv, hb⟩ := h1 σ
    have h3 : ∀ s : TanM (tau hU ≫ Z.π) (Y Z.i).t.G, ∃! a : Fin n → Γ(Z.X, U), s = ∑ i, a i • tanOf (x := tau hU ≫ Z.π) (hv i) :=
      fun s => (existsUnique_congr fun a => isComb_iff (fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) a s).1 (hb _ (isTan_tv s))
    let b : Module.Basis (Fin n) Γ(Z.X, U) (TanM (tau hU ≫ Z.π) (Y Z.i).t.G) :=
      Module.Basis.mk (v := fun i => tanOf (x := tau hU ≫ Z.π) (hv i)) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
        ((h3 0).unique ha.symm (by simp : (0 : TanM (tau hU ≫ Z.π) (Y Z.i).t.G) =
          ∑ i, (0 : Fin n → Γ(Z.X, U)) i • tanOf (x := tau hU ≫ Z.π) (hv i)))) fun s _ => by
        obtain ⟨a, rfl, -⟩ := h3 s
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨n, basPull _ ez b, q, fun j => ?_⟩
    rw [basPull_apply, Module.Basis.mk_apply]
    exact congrArg _ (tan_ext (hq j))
  · have ew : spMap (φ.comp (ev z U hz)) ≫ hU.fromSpec = w := by
      rw [← spMap_comp', Category.assoc, spMap_ev, e]
    have h4 := h2 K (φ.comp (ev z U hz)) (ew ▸ hw)
    rw [ew, ← Vecs.bc_bc] at h4
    let T : TVecs Dw (Y Z.i).t (w ≫ Z.π) := fun σ i => tanPull φ e' (tanPull (ev z U hz) ez (tanOf (ht σ i)))
    have h6 : up T = (fr.bc (ev z U hz)).bc φ := rfl
    rw [← h6, ← atlasOf_flagAt] at h4
    have h5 : ∀ j ∈ Z.ty σ, initSpan K (T σ) j = initSpan K (u σ) j := fun j hj =>
      Atlas.FlagAt.initSpan_eq h4 ((atlasOf_flagAt Z w _).2 hu) σ hj
    show initSpan K (T σ) j = _
    rw [hZ.1] at h5
    rcases le_total j (Dw.mult σ) with hj | hj
    · exact h5 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    · rw [initSpan_of_le _ hj, initSpan_of_le _ hj, ← initSpan_of_le _ le_rfl, ← initSpan_of_le _ le_rfl]
      exact h5 _ (Finset.mem_range.2 (Nat.lt_succ_self _))

theorem locMaps_closure {i : Idx H p} {X : Scheme.{0}} {π : X ⟶ (Y i).X} {ty : (E →+* ℂ) → Finset ℕ}
    {A : Atlas (Y i) π ty} {σ : E →+* ℂ} {k r : ℕ} (D : Adapted A σ k) (hk : k < Dw.mult σ) {Sb : D.C.Sub A.ch r}
    (Cl : Sb.Closure (π ≫ (Y i).s)) {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y i) (Cl.f ≫ π) ty'} {Z : Mdl Y i₀}
    {g : Z.X ⟶ X} (hS : StepRel D hk Cl.L A') (hZ : HasDR Z) (hg : MapsTo Z A g) : LocMaps Z A' := by
  intro K _ w hw
  obtain ⟨τ, mu, u, htr, hwτ, hu, hA⟩ := hg K w hw
  obtain ⟨u, rfl⟩ := Atlas.FlagAt.exists_up (A := atlasOf Z) hu
  obtain ⟨y, hy, hA'⟩ := hA.exists_point A'
  have e₁ : (w ≫ Z.π) ≫ τ = (y ≫ Cl.f) ≫ π := by rw [Category.assoc, ← hwτ, ← hy, Category.assoc]
  let u₁ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => pushE mu _ e₁ (u σ j)
  have hA₁ : A'.FlagAt y (up u₁) := hA'
  have hyf : y ≫ Cl.f = w ≫ g :=
    Atlas.FlagAt.point_eq ((hS K y u₁).1 hA₁).1 hA (by rw [← hy, Category.assoc])
  refine ⟨y, ⟨τ, mu, _, htr, hy.trans hwτ, hu, hA'⟩, fun R _ _ _ _ _ _ z ez => ?_⟩
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have e₂ : (z ≫ Z.π) ≫ τ = (z ≫ g) ≫ π := by
    have := projProper _ _ _ (Y i).proj
    have : (Y i).X.IsSeparated := ⟨by
      rw [← terminal.comp_from (Y i).s]
      infer_instance⟩
    have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
    refine ext_of_isDominant (spMap (algebraMap R K)) ?_
    simp only [Category.assoc] at hwτ ⊢
    rw [reassoc_of% ez, reassoc_of% ez, hwτ]
  have e₃ : spMap (algebraMap R K) ≫ z ≫ Z.π = w ≫ Z.π := by rw [reassoc_of% ez]
  have e₄ : spMap (algebraMap R K) ≫ z ≫ g = y ≫ Cl.f := by rw [reassoc_of% ez, hyf]
  have e₅ : spMap (algebraMap R K) ≫ (z ≫ g) ≫ π = (y ≫ Cl.f) ≫ π := by rw [← Category.assoc, e₄]
  obtain ⟨T, hT, hs⟩ := exists_int_frame hZ (algebraMap R K) z ez e₃ hw hu
  let T₁ : TVecs Dw (Y i).t ((z ≫ g) ≫ π) := fun σ j => pushE mu _ e₂ (T σ j)
  let T₂ : TVecs Dw (Y i).t ((y ≫ Cl.f) ≫ π) := fun σ j => tanPull (algebraMap R K) e₅ (T₁ σ j)
  have hT₁ : ∀ σ, ∃ (n : ℕ) (c : Module.Basis (Fin n) R (TanM ((z ≫ g) ≫ π) (Y i).t.G)) (q : Fin (Dw.mult σ) ↪ Fin n),
      (∀ j, c (q j) = T₁ σ j) ∧ T₂ σ = fun j => basPull (algebraMap R K) e₅ c (q j) := fun σ => by
    obtain ⟨n, c, q, hq⟩ := hT σ
    have : ∀ j, c.map (pushE mu _ e₂) (q j) = T₁ σ j := fun j => by rw [Module.Basis.map_apply, hq]
    exact ⟨n, _, q, this, funext fun j => by rw [basPull_apply, this]⟩
  have hA₂ : A'.FlagAt y (up T₂) := by
    refine flagAt_of_initSpan_eq (Category.assoc _ _ _).symm hA₁ (fun σ => ?_) fun σ j => ?_
    · obtain ⟨n, c, q, -, h⟩ := hT₁ σ
      rw [h]
      exact (basPull _ e₅ c).linearIndependent.comp _ q.injective
    · have : T₂ σ = fun j => (pushE mu _ e₁).toLinearMap (tanPull (algebraMap R K) e₃ (T σ j)) :=
        funext fun j => tan_ext (Category.assoc _ _ _).symm
      rw [this, initSpan_map, hs]
      exact (initSpan_map (pushE mu _ e₁).toLinearMap _ _).symm
  obtain ⟨hA₃, hc⟩ := (hS K y T₂).1 hA₂
  obtain ⟨α, hα⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing (U := D.C.B)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (D.C.cover x)) (z ≫ g)
  have hα' : ⊤ ≤ (y ≫ Cl.f) ⁻¹ᵁ D.C.B α := e₄ ▸ le_preimage_comp _ hα
  refine Cl.lift R K (z ≫ g) α hα (crd (D.b α) (z ≫ g) hα (T₁ σ ⟨k, hk⟩)) ?_ y e₄.symm fun h => ?_
  · obtain ⟨n, c, q, hq, h⟩ := hT₁ σ
    rw [← hq]
    refine exists_isUnit_repr _ c _ fun j => hinj ?_
    rw [← basPull_repr _ e₅, map_zero, tanPull_basAt _ _ _ _ e₄ hα']
    refine repr_eq_zero_of_mem _ q hk ?_
    rw [← h, D.int α K _ hα' T₂ hA₃ k le_rfl]
    exact Submodule.subset_span ⟨j, j.2, rfl⟩
  · have := hc α h
    convert this using 1
    exact funext fun j => (basAt_repr _ _ _ hα e₄ h e₅ _ _).symm

end GlobalTheory.DRFlag.StepLift

theorem GlobalTheory.DRFlag.locMaps_closure_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hk _ Cl _ _ _ _ => GlobalTheory.DRFlag.StepLift.locMaps_closure D hk Cl
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_closure_local_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' := by
  atlas_forward_decl GlobalTheory.DRFlag.locMaps_closure_of_hasDR
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem initSpan_self {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (v : Fin m → N) :
    initSpan R v m = Submodule.span R (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem flagAt_of_intOn (A : Atlas M π ty) (hty : ∀ σ, ∀ j ∈ ty σ, j ≤ Dw.mult σ)
    {U : (E →+* ℂ) → X.Opens} {hU : ∀ σ, IsAffineOpen (U σ)} {m : (E →+* ℂ) → ℕ}
    (b : ∀ σ, Module.Basis (Fin (Dw.mult σ) ⊕ Fin (m σ)) Γ(X, U σ) (TanM (tau (hU σ) ≫ π) M.t.G))
    (hb : ∀ σ, IntOn A σ (Dw.mult σ) (hU σ) (b σ)) {K : Type} [Field K] (w : Sp K ⟶ X)
    (hw : ∀ σ, ⊤ ≤ w ⁻¹ᵁ U σ) (hc : Set.range w ⊆ A.ch.carrier) :
    A.FlagAt w (up (Dw := Dw) fun σ i => basAt (b σ) w (hw σ) (.inl i)) := by
  obtain ⟨a, φ, e⟩ := A.ch.exists_fac w (hc ⟨_, rfl⟩)
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have f₀ := A.isFrame_bc e
  have g₀ := A.flagAt_fr e
  rw [← h₀] at f₀ g₀
  refine (A.flagAt_iff e h₀ _).2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨?_, ?_⟩,
    fun σ j hj => (hb σ K w (hw σ) u₀ g₀ j (hty σ j hj)).symm⟩
  · exact (basAt (b σ) w (hw σ)).linearIndependent.comp _ Sum.inl_injective
  · rw [← initSpan_self, ← hb σ K w (hw σ) u₀ g₀ _ le_rfl, initSpan_self]
    exact ((isFrame_up_iff _ _).1 f₀ σ).2

theorem hasDR_of_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hty hs
  refine ⟨hty, fun x => ?_⟩
  choose U hU m b hx hb using fun σ => hs σ x
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ⋂ σ, (U σ : Set Z.X) from Set.mem_iInter.2 hx) (isOpen_iInter_of_finite fun σ => (U σ).isOpen)
  have hle' : ∀ σ, U₀ ≤ U σ := fun σ q hq => Set.mem_iInter.1 (hle hq) σ
  let b' := fun σ => basAt (b σ) (tau hU₀) (tau_le hU₀ (hle' σ))
  refine ⟨U₀, hU₀, up (Dw := Dw) fun σ i => b' σ (.inl i), hx₀, fun σ => ?_, fun k _ φ hr => ?_⟩
  · let b'' := (b' σ).reindex finSumFinEquiv
    refine ⟨_, fun i => (tv (b'' i)).left, Fin.castAddEmb _, fun i => ?_, fun i => isTan_tv _, fun u hu => ?_⟩
    · simp only [b'', Module.Basis.reindex_apply, Fin.castAddEmb_apply, finSumFinEquiv_symm_apply_castAdd]
      rfl
    · exact (existsUnique_congr fun a => isComb_iff b'' a (tanOf hu)).2
        ⟨b''.repr (tanOf hu), (b''.sum_repr _).symm, fun a ha => by rw [ha]; exact (b''.repr_sum_self a).symm⟩
  · have hw : ∀ σ, ⊤ ≤ (spMap φ ≫ tau hU₀) ⁻¹ᵁ U σ := fun σ => le_preimage_comp _ (tau_le hU₀ (hle' σ))
    have key := flagAt_of_intOn (atlasOf Z) (fun σ j hj => by rw [hty, Finset.mem_range] at hj; omega)
      b hb (spMap φ ≫ tau hU₀) hw (by rw [(atlasOf Z).cover]; exact hr)
    rw [← up_tanPull φ (Category.assoc _ _ _).symm]
    simp only [b', tanPull_basAt _ φ _ _ rfl (hw _)]
    exact key

end GlobalTheory.DRFlag
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDR_of_full_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  atlas_forward_decl GlobalTheory.DRFlag.hasDR_of_intStep
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_cocycle_embedding : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ∀ C : Coc Z, ∃ (Γ : Type) (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ g, IsAffineOpen (D g)) (cover : ∀ x : Z, ∃ g, x ∈ D g) (le : ∀ g, D g ≤ C.B (a g)) (N : ℕ), Nonempty ((C.refine a D aff cover le).Emb N) := by
  first | exact @GlobalTheory.DRFlag.Coc.exists_refine_emb | exact GlobalTheory.DRFlag.Coc.exists_refine_emb | (intros; apply GlobalTheory.DRFlag.Coc.exists_refine_emb <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem basAt_basAt_tau {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {Z : Scheme.{0}} {π : Z ⟶ X} {U U' : Z.Opens}
    {hU : IsAffineOpen U} (hU' : IsAffineOpen U') (le : U' ≤ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U') :
    basAt (hU := hU') (basAt b (tau hU') (tau_le hU' le)) w hw =
      basAt b w (le_preimage_mono le hw) := by
  refine Module.Basis.eq_of_apply_eq fun i => ?_
  rw [basAt, basPull_apply]
  exact tanPull_basAt b _ _ _ (by rw [tau, spMap_ev]) _ _ i

theorem exists_adapted_emb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → Nonempty (Adapted A σ k) → ∃ (D : Adapted A σ k) (N : ℕ), Nonempty (D.C.Emb N) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k hG ⟨D⟩
  obtain ⟨Γ, a, B, aff, cover, le, N, hN⟩ := GlobalTheory.T.exists_refined_cocycle_embedding V X (π ≫ M.s) hG.proj D.C
  refine ⟨{ C := D.C.refine a B aff cover le
            b := fun g => basAt (D.b (a g)) (tau (aff g)) (tau_le (aff g) (le g))
            int := fun g K _ w hw u hu j hj => ?_
            coord := fun g d S _ z hg hd v => ?_ }, N, hN⟩
  · have := D.int (a g) K w (le_preimage_mono (le g) hw) u hu j hj
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) w hw] at this
    exact this
  · have := D.coord (a g) (a d) S z (le_preimage_mono (le g) hg) (le_preimage_mono (le d) hd) v
    rw [← D.C.refine_tr a B aff cover le g d z hg hd] at this
    unfold crd at this
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) z hg, ← basAt_basAt_tau (aff d) (le d) (D.b (a d)) z hd] at this
    exact this

end GlobalTheory.DRFlag
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → Nonempty (Adapted A σ k) → ∃ (D : Adapted A σ k) (N : ℕ), Nonempty (D.C.Emb N) := by
  atlas_forward_decl GlobalTheory.DRFlag.exists_adapted_emb
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Retype

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_insert_zero {X₀ : Scheme.{0}} {t : SAB H X₀} {R : Type} [CommRing R] (x : Sp R ⟶ X₀)
    (u u' : Vecs Dw t R) : SameFlag (fun σ => insert 0 (ty σ)) t x u u' ↔ SameFlag ty t x u u' := by
  refine ⟨fun h σ k hk => h σ k (Finset.mem_insert_of_mem hk), fun h σ k hk i hi => ?_⟩
  rcases Finset.mem_insert.1 hk with rfl | hk
  · exact absurd hi (Nat.not_lt_zero _)
  · exact h σ k hk i hi

theorem flagAt_insert_zero (A : PreAtlas M X) {K : Type} [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K) :
    A.FlagAt π (fun σ => insert 0 (ty σ)) w u ↔ A.FlagAt π ty w u := by
  simp only [PreAtlas.FlagAt, sameFlag_insert_zero]

def Atlas.addZero (A : Atlas M π ty) : Atlas M π (fun σ => insert 0 (ty σ)) where
  toPreAtlas := A.toPreAtlas
  cover := A.cover
  alg_s := A.alg_s
  smooth := A.smooth
  frame := A.frame
  glue k _ a a' φ φ' h := (sameFlag_insert_zero _ _ _).2 (A.glue k a a' φ φ' h)
  bij k _ f y hy u hu := by
    simp only [flagAt_insert_zero]
    exact A.bij k f y hy u hu

end Retype

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def PiLocalization₂ (Z : Mdl Y i₀) (k : (E →+* ℂ) → ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (π : X ⟶ (Y Z.i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y Z.i) π ty) (f : X ⟶ Z.X),
    Geo (Y Z.i) π ∧ f ≫ Z.π = π ∧ (∀ σ, Z.ty σ ⊆ ty σ) ∧ (∀ σ, ty σ ⊆ Finset.range (Dw.mult σ + 1)) ∧
    (∀ σ, Finset.range (k σ + 1) ⊆ ty σ) ∧ (∀ σ, IntStep A σ (k σ)) ∧
    (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u → (atlasOf Z).FlagAt (w ≫ f) u) ∧
    ∀ Z'' : Mdl Y i₀, HasDR Z'' → (∃ g, IsMap Z'' Z g) → ∃ h, MapsTo Z'' A h

theorem stage_zero (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) : PiLocalization₂ Z fun _ => 0 := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  refine ⟨Z.X, Z.π, _, (atlasOf Z).addZero, 𝟙 _, geoOf Z, Category.id_comp _, fun σ => Finset.subset_insert _ _,
    fun σ => Finset.insert_subset (by simp) (hZ σ), fun σ => by simp, fun σ => GlobalTheory.T.atlas_integral_at_index_zero E H Dw _ _ _ _ _ _ _ _ _ σ,
    fun K _ w u h => ?_, fun Z'' _ ⟨g, hg⟩ => ⟨g, fun k _ w hw => ?_⟩⟩
  · rw [Category.comp_id]
    exact (flagAt_insert_zero _ w u).1 h
  · obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg.2 k w hw
    exact ⟨τ, mu, u, h1, h2, h3, (flagAt_insert_zero _ _ _).2 h4⟩

theorem stage_succ (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {k k' : (E →+* ℂ) → ℕ} (σ : E →+* ℂ)
    (hk : k σ < Dw.mult σ) (h₁ : k' σ = k σ + 1) (h₂ : ∀ σ', σ' ≠ σ → k' σ' = k σ') (h : PiLocalization₂ Z k) : PiLocalization₂ Z k' := by
  classical
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨X, π, ty, A₀, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := h
  obtain ⟨D₀, N, hEm⟩ := GlobalTheory.T.exists_adapted_embedding E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo
    (GlobalTheory.T.nonempty_adapted_of_intStep E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo (int σ))
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.T.exists_atlas_refining_cocycle E H Dw _ _ _ _ _ _ _ _ A₀ D₀.C
  let D : Adapted A σ (k σ) :=
    ⟨D₀.C, D₀.b, fun a K _ w hw u hu => D₀.int a K w hw u ((hA K w _).1 hu), D₀.coord⟩
  have ex : ∃ r, k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := ⟨Dw.mult σ - k σ - 1, Or.inr (by omega)⟩
  let r := Nat.find ex
  have hr : k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := Nat.find_spec ex
  have hj : k σ + r + 1 ≤ Dw.mult σ := by
    rcases hr with h | h
    · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 (s₂ σ h))
    · exact h.le
  have gap : ∀ e ∈ ty σ, e ≤ k σ ∨ k σ + r + 1 ≤ e := fun e he => by
    by_cases h : e ≤ k σ
    · exact Or.inl h
    · have : r ≤ e - k σ - 1 := Nat.find_min' ex (Or.inl (by rwa [show k σ + (e - k σ - 1) + 1 = e by omega]))
      exact Or.inr (by omega)
  obtain ⟨Sb, hSb⟩ := GlobalTheory.T.adapted_next_step_type E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hr α hα
  obtain ⟨Cl⟩ := GlobalTheory.T.nonempty_closure_of_embedding _ X (π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat D.C N hEm A.ch r Sb
  let ty' := Function.update ty σ (insert (k σ + 1) (ty σ))
  have t₁ : ty' σ = insert (k σ + 1) (ty σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ σ → ty' σ' = ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.adapted_substep_closure E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hk Sb Cl ty' hSb hr gap t₁ t₂
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ Cl.Z') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      A₀.FlagAt (w ≫ Cl.f) u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := id hu
    rw [← Category.assoc] at hfr
    obtain ⟨U, rfl⟩ := exists_up fun σ i => (hfr.1 σ i).1
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have geo' : Geo (Y Z.i) (Cl.f ≫ π) :=
    ⟨by rw [Category.assoc]; exact Cl.proj, Cl.normal, by rw [Category.assoc]; exact Cl.flat, A'.cover ▸ by
      rw [A'.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← A.cover, ← Cl.carrier_eq]
      exact Cl.dense⟩
  have s₂' : ∀ σ', ty' σ' ⊆ Finset.range (Dw.mult σ' + 1) := fun σ' => by
    by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact Finset.insert_subset (Finset.mem_range.2 (by omega)) (s₂ _)
    · rw [t₂ σ' e]; exact s₂ σ'
  refine ⟨Cl.Z', Cl.f ≫ π, ty', A', Cl.f ≫ f, geo', by rw [Category.assoc, hf], fun σ' => ?_, s₂', fun σ' => ?_,
    fun σ' => ?_, fun K _ w u hu => ?_, fun Z'' hd hg => ?_⟩
  · by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact (s₁ _).trans (Finset.subset_insert _ _)
    · rw [t₂ σ' e]; exact s₁ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [t₁, h₁, Finset.range_add_one]
      exact Finset.insert_subset_insert _ (s₃ _)
    · rw [t₂ σ' e, h₂ σ' e]; exact s₃ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [h₁]
      exact GlobalTheory.T.adapted_linear_pullback E H Dw _ _ _ _ _ _ _ _ A σ' (k σ') D hk _ Cl.f Cl.L ty' A' rel
    · rw [h₂ σ' e]
      exact GlobalTheory.T.atlas_pullback_preserves_step E H Dw _ _ _ _ _ _ _ _ A₀ σ' (k σ') _ Cl.f ty' A' down (int σ')
  · rw [← Category.assoc]
    exact fl K _ u (down K w u hu)
  · obtain ⟨g, hg'⟩ := mn Z'' hd hg
    obtain ⟨g₀, hc, -⟩ := hg
    have hg'' : MapsTo Z'' A g := fun K _ w hw => by
      obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg' K w hw
      exact ⟨τ, mu, u, h1, h2, h3, (hA K _ _).2 h4⟩
    exact GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hc.2.1 (fun σ' => hd.1 σ' ▸ s₂' σ')
      (GlobalTheory.T.adapted_closure_local_system E H Dw Xo p W Y i₀ Z.i X π ty A σ (k σ) r D hk Sb Cl ty' A' Z'' g rel hd hg'')

theorem stage_all (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) (n : ℕ) :
    ∀ k : (E →+* ℂ) → ℕ, (∀ σ, k σ ≤ Dw.mult σ) → ∑ σ, k σ = n → PiLocalization₂ Z k := by
  classical
  induction n with
  | zero =>
    intro k _ h
    obtain rfl : k = fun _ => 0 := funext fun σ => Finset.sum_eq_zero_iff.1 h σ (Finset.mem_univ _)
    exact stage_zero hp hW Z hZ
  | succ n ih =>
    intro k hk h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ n.succ_ne_zero : ∑ σ, k σ ≠ 0)
    have e₁ : Function.update k σ (k σ - 1) σ = k σ - 1 := Function.update_self _ _ _
    refine stage_succ hp hW Z (k := Function.update k σ (k σ - 1)) σ (by have := hk σ; omega) (by omega)
      (fun σ' e => (Function.update_of_ne e _ _).symm) (ih _ (fun σ' => ?_) ?_)
    · by_cases e : σ' = σ
      · subst e; have := hk σ'; omega
      · rw [Function.update_of_ne e]; exact hk σ'
    · rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ), Finset.erase_eq] at h
      omega

theorem exists_isDRFlag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ Z : Mdl Y i₀, (∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) → ∃ Z', IsDRFlag Z Z' := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z hZ
  obtain ⟨X, π, ty, A, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := stage_all hp hW Z hZ _ Dw.mult (fun _ => le_rfl) rfl
  obtain ⟨Z', e, hi, hty, m₁, m₂, m₃⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X π ty A Z.dvd Z.le geo
  have full : ∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1) := fun σ => hty ▸ (s₂ σ).antisymm (s₃ σ)
  refine ⟨Z', hi, GlobalTheory.T.hasDR_of_full_intStep E H Dw Xo p W Y i₀ Z' full fun σ => m₃ σ _ (int σ),
    ⟨e.hom ≫ f, ⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ s₁⟩, m₂ _ _ _ (atlasOf Z) f hf fl⟩,
    fun Z'' hd hg => ?_⟩
  obtain ⟨h, hh⟩ := mn Z'' hd hg
  obtain ⟨g, hc, -⟩ := hg
  exact ⟨h ≫ e.inv, ⟨hi ▸ hc.1, hi ▸ hc.2.1, fun σ => by rw [full, hd.1]⟩, m₁ Z'' h hh⟩

end GlobalTheory.DRFlag
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_de_rham_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ Z : Mdl Y i₀, (∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) → ∃ Z', IsDRFlag Z Z' := by
  atlas_forward_decl GlobalTheory.DRFlag.exists_isDRFlag
end
