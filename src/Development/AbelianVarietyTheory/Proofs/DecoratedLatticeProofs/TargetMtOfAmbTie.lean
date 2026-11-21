import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatHermHermUnitAniso
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

namespace GramPlacesCS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem map_gramR {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K) (σ : K →+* ℂ) :
    σ (gramR G e) =
      ((StepBAux.fmat (Rb.tw σ) e)ᴴ * G.map σ * StepBAux.fmat σ e).det := by
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, StepBAux.fmat, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum,
    map_mul, Rb.tw_apply, Complex.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [NumberField K] [StarRing K] in

theorem det_conjugate {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K)
    (φ : K →+* ℂ) :
    ((StepBAux.fmat (ComplexEmbedding.conjugate φ) e)ᴴ * G.map (ComplexEmbedding.conjugate φ) *
        StepBAux.fmat (ComplexEmbedding.conjugate φ) e).det =
      starRingEnd ℂ (((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det) := by
  have hE : StepBAux.fmat (ComplexEmbedding.conjugate φ) e =
      (StepBAux.fmat φ e).map (starRingEnd ℂ) := by
    ext i a; simp [StepBAux.fmat, ComplexEmbedding.conjugate_coe_eq]
  have hG : G.map (ComplexEmbedding.conjugate φ) = (G.map φ).map (starRingEnd ℂ) := by
    ext i a; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hE, hG, Rb.conjT_map_conj, ← Matrix.map_mul, ← Matrix.map_mul,
    RingHom.map_det, RingHom.mapMatrix_apply]

theorem gram_eq (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    gram X v e =
      (StepBAux.fmat v.embedding e)ᴴ * G.map v.embedding * StepBAux.fmat v.embedding e := by
  rw [StepBAux.gram_eq_fmat, StepBAux.met, (hX.2 v).2]

theorem gram_mk_re (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (φ : K →+* ℂ) :
    (gram X (InfinitePlace.mk φ) e).det.re =
      ((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det.re := by
  rw [gram_eq K0 G X hX]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, det_conjugate, Complex.conj_re]

theorem map_posDef (K0 : Subfield K) {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (v : InfinitePlace K) : (G.map v.embedding).PosDef := by
  rw [← (hX.2 v).2]
  exact Rb.metMat_posDef X v (hX.2 v).1

theorem gram_det_re_nonneg (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  rw [gram_eq K0 G X hX]
  have h := ((map_posDef K0 G X hX v).posSemidef.conjTranspose_mul_mul_same
    (StepBAux.fmat v.embedding e)).det_nonneg
  exact (Complex.le_def.mp h).1

theorem place_sq_le (K0 : Subfield K) (hK0 : IsCMSub K0) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    ‖v.embedding (gramR G e)‖ ^ 2 ≤ (gram X (Rb.plc v) e).det.re * (gram X v e).det.re := by
  have h := determinant_cauchy_schwarz n j _ (map_posDef K0 G X hX v)
    (StepBAux.fmat (Rb.tw v.embedding) e)ᴴ (StepBAux.fmat v.embedding e)ᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [map_gramR, Rb.plc, gram_mk_re K0 G X hX, Rb.Hmap_tw K0 hK0 G hX.1, gram_eq K0 G X hX]
  exact h

end GramPlacesCS

open GramPlacesCS in

theorem prod_norm_gramR_le_prod_gram_det :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n j : ℕ) (G : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 G X → ∀ e : Fin j → Fin n → K,
      ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ≤
        ∏ v : InfinitePlace K, (gram X v e).det.re := by
  intro K _ _ _ K0 hK0 n j G X hX e
  have hperm : ∏ v : InfinitePlace K, (gram X (Rb.plc v) e).det.re =
      ∏ v : InfinitePlace K, (gram X v e).det.re :=
    Equiv.prod_comp (Function.Involutive.toPerm _ Rb.plc_plc) (fun v => (gram X v e).det.re)
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
    calc (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2
        = ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ^ 2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ v : InfinitePlace K, ((gram X (Rb.plc v) e).det.re * (gram X v e).det.re) :=
        Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => place_sq_le K0 hK0 G X hX e v)
      _ = (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
        rw [Finset.prod_mul_distrib, hperm, sq]
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun v _ => gram_det_re_nonneg K0 G X hX e v) two_ne_zero).mp hsq

end GlobalTheory
end
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lcv_nonneg_of_integral_full :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (j : ℕ) (Γ : Matrix (Fin j) (Fin j) K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (L : Submodule (𝓞 K) (Fin j → K)), (∀ v, IsUnit (Y v).det) → Submodule.IsLattice K L → Γ.det ≠ 0 → Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform Γ) L → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram Y v (fun i => (Pi.single i 1 : Fin j → K))).det.re) → 0 ≤ lcv Y L := by
  intro K _ _ _ _ j Γ Y L hY hL hΓ hint hle
  have h := GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j Y hY Γ 1 one_pos hΓ hle L hL (by
    intro x hx y hy
    have h1 := hint x hx y hy
    rw [RationalHermitianForm.hform_eq_dot] at h1
    simpa using h1)
  simpa using h

end GlobalTheory
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SpanLattice

open Formalism.L2.GlobalTheoryTheory.HLatOps

theorem exists_fullLattice_of_fg :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
      (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
      ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG →
      ∃ (j : ℕ) (e : Fin j → Fin n → K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ)
        (L : Submodule (𝓞 K) (Fin j → K)), LinearIndependent K e ∧ (∀ v, IsUnit (Y v).det) ∧
        Submodule.IsLattice K L ∧ (∀ x : Fin j → K, x ∈ L ↔ ∑ i, x i • e i ∈ N) ∧
        (∀ v, gram Y v (fun i => (Pi.single i 1 : Fin j → K)) = gram X v e) ∧
        lcv Y L = lcv X N := by
  intro K _ _ _ n X hX N hN
  set U : Submodule K (Fin n → K) := Submodule.span K (N : Set (Fin n → K)) with hU
  let c := Module.finBasis K U
  let e : Fin (finrank K U) → Fin n → K := fun i => (c i : Fin n → K)
  let ψ : (Fin (finrank K U) → K) →ₗ[K] (Fin n → K) := U.subtype ∘ₗ c.equivFun.symm.toLinearMap
  have hψ : ∀ x, ψ x = ∑ i, x i • e i := by
    intro x
    simp [ψ, e, Basis.equivFun_symm_apply]
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype U).comp c.equivFun.symm.injective
  have hrange : ∀ y ∈ U, ∃ x, ψ x = y := fun y hy =>
    ⟨c.equivFun ⟨y, hy⟩, by simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply]⟩
  have hmemU : ∀ x, ψ x ∈ U := fun x => (c.equivFun.symm x).2
  have hsingle : ∀ i, ψ (Pi.single i 1) = e i := by
    intro i
    rw [hψ, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  let L : Submodule (𝓞 K) (Fin (finrank K U) → K) := N.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L.map (ψ.restrictScalars (𝓞 K)) = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hrange y (Submodule.subset_span hy)
      exact ⟨x, hy, rfl⟩
  have hfg : L.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hinj (by rw [hmap]; exact hN)
  have hS := isSesq_comp (isSesq_maj (Pi.basisFun K (Fin n)) X) ψ
  have hP := posAt_comp (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin (finrank K U)))
    (isSesq_maj (Pi.basisFun K (Fin n)) X) (posAt_maj (Pi.basisFun K (Fin n)) X hX) ψ hinj
  obtain ⟨h1, h2, h3⟩ := of_form_spec K _ _ (Pi.basisFun K (Fin (finrank K U))) L _ hS hP
  let Y : InfinitePlace K → Matrix (Fin (finrank K U)) (Fin (finrank K U)) ℂ := fun v =>
    frameOf (gramOf (Pi.basisFun K (Fin (finrank K U)))
      (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)))
  have hY : ∀ v, IsUnit (Y v).det := h1
  have hm : ∀ v x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (finrank K U))) Y v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y) := h2
  have hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (finrank K U))) Y v x := fun v x => by
    rw [normAt_eq_sqrt (Pi.basisFun K (Fin n)) X v (ψ x)]
    exact (h3 v x).symm
  refine ⟨finrank K U, e, Y, L, ?_, hY, ⟨hfg, ?_⟩, fun x => ?_, fun v => ?_, ?_⟩
  · exact c.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · rw [eq_top_iff]
    intro x _
    have hsp : Submodule.span K (N : Set (Fin n → K)) =
        (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [Submodule.map_span, ← hmap]
      rfl
    have hx : ψ x ∈ (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [← hsp]
      exact hmemU x
    obtain ⟨y, hy, hxy⟩ := hx
    exact hinj hxy ▸ hy
  · rw [← hψ]
    rfl
  · ext a b
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, hm, hsingle]
  · have h := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin (finrank K U))) Y
      (Pi.basisFun K (Fin n)) X ψ hY hX hinj hn L hfg).1
    rw [hmap] at h
    unfold lcv
    rw [h]

end GlobalTheory.SpanLattice
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem hform_gramMatrix {K : Type} [Field K] [StarRing K] {n j : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K) (x y : Fin j → K) :
    hform (Matrix.of fun a b => star (e a) ⬝ᵥ G *ᵥ e b) x y
      = hform G (∑ i, x i • e i) (∑ i, y i • e i) := by
  have h : ∀ a b, hform G (e a) (e b) = star (e a) ⬝ᵥ G *ᵥ e b := by
    intro a b
    simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
      smul_eq_mul, RingHom.id_apply, Pi.star_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, h,
    RingHom.id_apply]
  rw [hform, Matrix.toLinearMapₛₗ₂'_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_eq_mul, Finset.mul_sum, RingHom.id_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => by ring

theorem lcv_nonneg_of_integral_submodule (K : Type) [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] (K0 : Subfield K) (hK0 : IsCMSub K0) (v0 : InfinitePlace K)
    (hv0 : IsConjAt v0) (n : ℕ) (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hGX : IsRatHerm K0 G X)
    (N : Submodule (𝓞 K) (Fin n → K)) (hN : N.FG)
    (hint : Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform G) N) : 0 ≤ lcv X N := by
  obtain ⟨j, e, Y, L, he, hY, hL, hmem, hgram, hlcv⟩ :=
    GlobalTheory.SpanLattice.exists_fullLattice_of_fg K n X (fun v => (hGX.2 v).1) N hN
  rw [← hlcv]
  refine GlobalTheory.lcv_nonneg_of_integral_full K j (Matrix.of fun a b => star (e a) ⬝ᵥ G *ᵥ e b) Y L hY hL ?_ ?_ ?_
  · exact (GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n j G X hGX).2.2 e he
  · intro x hx y hy
    rw [hform_gramMatrix]
    exact hint _ ((hmem x).1 hx) _ ((hmem y).1 hy)
  · simp only [hgram]
    exact GlobalTheory.prod_norm_gramR_le_prod_gram_det K K0 hK0 n j G X hGX e

end GlobalTheory
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_covolume_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 G X → ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG → Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform G) N → 0 ≤ lcv X N := by
  atlas_forward_decl GlobalTheory.lcv_nonneg_of_integral_submodule
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData in

theorem muMax_nonpos_of_lcv_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K), (∀ v, IsUnit (A.X v).det) → A.L.FG → A.L ≠ ⊥ → (∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N ≠ ⊥ → 0 ≤ (Formalism.L2.GlobalTheoryTheory.HLatOps.withL A N).lcv) → A.muMax ≤ 0 := by
  intro K _ _ _ _ A hX hL hL0 h
  unfold HLat.muMax
  refine muMaxDef_le A.b A.X hL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := fg_of_le hL hQ
  have hl := h Q hQ hQ0
  simp only [HLat.lcv, Formalism.L2.GlobalTheoryTheory.HLatOps.withL] at hl
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos'
  have h2 : (0 : ℝ) < 2 / (Module.finrank ℚ K : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (ht A.b A.X Q) := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_pos_of_neg h2 hc
    linarith
  rw [muDef_eq_log A.b A.X hX hQfg hQ0]
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hr : (0 : ℝ) < (rkK Q : ℝ) := by exact_mod_cast rkK_pos hQ0
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity

end GlobalTheory
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

theorem dualForm_ringHom_inv {F E : Type} [Field F] [Field E] (f : F →+* E) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : A⁻¹.map f = (A.map f)⁻¹ := by
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ (map_zero f) (map_one f)]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [show (A.map f).det = f A.det by rw [RingHom.map_det, RingHom.mapMatrix_apply]]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0
      exact hu (by rw [h0, map_zero])
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h']
    ext i j
    simp

theorem dualForm_inv_mem_subfield {K : Type} [Field K] (K0 : Subfield K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0) (i j : Fin n) : H⁻¹ i j ∈ K0 := by
  set H0 : Matrix (Fin n) (Fin n) K0 := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hmap : H0.map K0.subtype = H := by ext a b; rfl
  rw [← hmap, ← dualForm_ringHom_inv]
  exact (H0⁻¹ i j).2

theorem isRatHerm_dualFrame (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K)
    (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :
    IsRatHerm K0 H X → IsRatHerm K0 (H⁻¹)ᵀ (Formalism.HN.dualFrame X) := by
  rintro ⟨hK0, hX⟩
  refine ⟨fun i j => dualForm_inv_mem_subfield K0 H hK0 j i, fun v => ?_⟩
  obtain ⟨hu, hm⟩ := hX v
  have huT : IsUnit ((X v)ᵀ).det := by rwa [Matrix.det_transpose]
  have hD : Formalism.HN.dualFrame X v = ((X v)ᵀ)⁻¹ := rfl
  rw [hD]
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_nonsing_inv]
    exact huT.ringInverse
  · rw [Matrix.nonsing_inv_nonsing_inv _ huT, Matrix.transpose_map,
      dualForm_ringHom_inv, ← hm, Matrix.mul_inv_rev, Matrix.conjTranspose_nonsing_inv,
      Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.transpose_mul]
    have hcu : IsUnit (X v)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
    rw [Matrix.nonsing_inv_nonsing_inv _ hcu]
    congr 1

end GlobalTheory
end
end

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualInt

theorem star_mem_one_O {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : star a ∈ (1 : Submodule (𝓞 K) K) := by
  rw [Submodule.mem_one] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
    have := (r.isIntegral_coe).map (starRingAut (R := K) : K ≃+* K).toRingHom.toIntAlgHom
    simpa using this
  exact ⟨⟨_, hi⟩, rfl⟩

theorem hform_eq_dot {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (a b : Fin n → K) :
    hform H a b = star a ⬝ᵥ H *ᵥ b := by
  simp [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_comm]

theorem inv_mulVec_star_mem_dual {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : IsUnit H.det) (M : Submodule (𝓞 K) (Fin n → K))
    (y : Fin n → K) (hy : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) :
    H⁻¹ *ᵥ star y ∈ Formalism.HermitianLatticesTheory.dual (hform H) M := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro x hx
  change hform H x (H⁻¹ *ᵥ star y) ∈ (1 : Submodule (𝓞 K) K)
  rw [hform_eq_dot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  have e : star x ⬝ᵥ star y = star (y ⬝ᵥ x) := by
    simp [dotProduct, mul_comm]
  rw [e]
  exact star_mem_one_O (hy x hx)

theorem dual_form_integral :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det → ∀ M : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → ∀ y y' : Fin n → K,
      (∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      (∀ x ∈ M, y' ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      hform (H⁻¹)ᵀ y y' ∈ (1 : Submodule (𝓞 K) K) := by
  intro K _ _ _ n H _ hH M hM y y' hy hy'
  have hz := hM (inv_mulVec_star_mem_dual H hH M y hy)
  have e : hform (H⁻¹)ᵀ y y' = y' ⬝ᵥ (H⁻¹ *ᵥ star y) := by
    rw [hform_eq_dot, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rw [e]
  exact hy' _ hz

end GlobalTheory.DualInt
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.IntegralDualSlope

variable {K : Type} [Field K] [NumberField K]

noncomputable def coordDual {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) (Fin n → K) :=
  (Formalism.HN.dualLat M).map
    ((Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap.restrictScalars (𝓞 K))

omit [NumberField K] in

theorem coords_dotProduct {n : ℕ} (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    (Pi.basisFun K (Fin n)).dualBasis.equivFun f ⬝ᵥ x = f x := by
  conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x, map_sum]
  simp [dotProduct, mul_comm]

theorem dotProduct_mem_one {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} {y : Fin n → K}
    (hy : y ∈ coordDual M) : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨f, hf, rfl⟩ := hy
  intro x hx
  obtain ⟨a, ha⟩ := hf x hx
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [ha]
  exact (coords_dotProduct f x).symm

theorem coordDual_spec [StarRing K] [IsTotallyComplex K] {n : ℕ} (hn : 0 < n)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det) :
    (coordDual M).FG ∧ coordDual M ≠ ⊥ ∧
      Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) (coordDual M) =
        Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
          (Formalism.HN.dualLat M) := by
  have hfg := Formalism.HN.DualPolygon.dualLat_fg M hM.span_eq_top
  have hinj : Function.Injective (Pi.basisFun K (Fin n)).dualBasis.equivFun.toLinearMap :=
    (Pi.basisFun K (Fin n)).dualBasis.equivFun.injective
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    have h := hM.span_eq_top
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Submodule.bot_coe, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  refine ⟨hfg.map _, fun h => ?_, ?_⟩
  · refine Formalism.HN.DualPolygon.dual_ne_bot (Pi.basisFun K (Fin n)) M hM.fg hM.span_eq_top hM0 ?_
    refine (Submodule.eq_bot_iff _).2 fun f hf => hinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ (Submodule.mem_map_of_mem hf)
  · have hu := Formalism.HN.DualPolygon.dualFrame_unit X hX
    have := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X)
      (Pi.basisFun K (Fin n)) (Formalism.HN.dualFrame X) _ hu hu hinj (fun v x => by
        unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
        simp) _ hfg).2.2.2.1
    unfold Formalism.HN.muMaxDef coordDual
    rw [this]

theorem muMaxDual_nonpos :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
      IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      IsRatHerm K0 H X → ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M →
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → 0 < n → (Formalism.L2.DIV.toHLat X M).muMaxDual ≤ 0 := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n H X hH M hM hle hn
  have hX : ∀ v, IsUnit (X v).det := fun v => (hH.2 v).1
  obtain ⟨hfg, hne, heq⟩ := coordDual_spec hn M hM X hX
  obtain ⟨hherm, hdet, -⟩ := GlobalTheory.ratHerm_herm_unit_aniso K K0 v0 hv0 n 0 H X hH
  have hG := GlobalTheory.isRatHerm_dualFrame K K0 n H X hH
  have hint := GlobalTheory.DualInt.dual_form_integral K n H hherm hdet M hle
  have key := GlobalTheory.muMax_nonpos_of_lcv_nonneg K (Formalism.L2.DIV.toHLat (Formalism.HN.dualFrame X) (coordDual M))
    (Formalism.HN.DualPolygon.dualFrame_unit X hX) hfg hne (fun N hN _ => by
      have hNfg : Submodule.FG (N : Submodule (𝓞 K) (Fin n → K)) :=
        (hfg.of_le hN)
      exact GlobalTheory.T.hermitian_lattice_covolume_nonneg K K0 hK0 v0 hv0 n _ _ hG N hNfg (fun y hy y' hy' =>
        hint y y' (dotProduct_mem_one (hN hy)) (dotProduct_mem_one (hN hy'))))
  exact heq.symm.trans_le key

end GlobalTheory.IntegralDualSlope
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_self_dual_max_slope : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), IsRatHerm K0 H X → ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → 0 < n → (Formalism.L2.DIV.toHLat X M).muMaxDual ≤ 0 := by
  atlas_forward_decl GlobalTheory.IntegralDualSlope.muMaxDual_nonpos
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SelfDualSlope

open Formalism.L2.GlobalTheoryTheory.HLatOps

theorem muMaxDual_nonpos_of_rat_coord : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (A : HLat K) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (e : (Fin n → K) ≃ₗ[K] A.V) (M : Submodule (𝓞 K) (Fin n → K)), A.Good → 0 < A.rank → (∀ i j, H i j ∈ K0) → (∀ (v : InfinitePlace K) (i j : Fin n), Formalism.HermitianLatticesTheory.majAt A.b A.X v (e (Pi.single i 1)) (e (Pi.single j 1)) = v.embedding (H i j)) → A.L = M.map (e.toLinearMap.restrictScalars (𝓞 K)) → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → A.muMaxDual ≤ 0 := by
  intro K _ _ _ _ K0 hK0 v0 hv0 A n H e M hG hr hH0 hgram hL hdual
  have hs : IsSesq (fun v (x y : Fin n → K) => Formalism.HermitianLatticesTheory.majAt A.b A.X v (e.toLinearMap x) (e.toLinearMap y)) :=
    isSesq_comp (isSesq_maj A.b A.X) e.toLinearMap
  have hg : ∀ v : InfinitePlace K, gramOf (Pi.basisFun K (Fin n))
      (fun (x y : Fin n → K) => Formalism.HermitianLatticesTheory.majAt A.b A.X v (e.toLinearMap x) (e.toLinearMap y)) =
      H.map v.embedding := by
    intro v
    ext i j
    simp only [gramOf, Matrix.of_apply, Pi.basisFun_apply, Matrix.map_apply]
    exact hgram v i j
  have hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := by
    intro v
    rw [← hg v]
    exact posAt_comp A.b (Pi.basisFun K (Fin n)) (isSesq_maj A.b A.X) (posAt_maj A.b A.X hG.1)
      e.toLinearMap e.injective v
  have hX := Formalism.L2.DIV.stdFrameRatHerm K K0 n H hH0 hpos
  let B : HLat K := Formalism.L2.DIV.toHLat (Formalism.L2.DIV.stdFrame H) M
  let I : Iso B A :=
    { e := e
      map_L := hL.symm
      norm := by
        intro v x
        rw [normAt_eq_sqrt, normAt_eq_sqrt]
        congr 2
        have h1 := sesq_eq_sum hs (Pi.basisFun K (Fin n)) v x x
        have h2 := sesq_eq_sum (isSesq_maj (Pi.basisFun K (Fin n)) (Formalism.L2.DIV.stdFrame H))
          (Pi.basisFun K (Fin n)) v x x
        rw [gramOf_maj] at h2
        have h3 : ((Formalism.L2.DIV.stdFrame H v)⁻¹).conjTranspose * (Formalism.L2.DIV.stdFrame H v)⁻¹ =
          H.map v.embedding := (Formalism.L2.DIV.frameOfSpec n _ (hpos v)).2
        rw [h3] at h2
        rw [hg v] at h1
        exact h1.trans h2.symm }
  have hB : B.Good := I.symm.good hG
  have hlat : Submodule.IsLattice K M := ⟨hB.2.1, hB.2.2⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      have h1 : B.rank = A.rank := I.rank_eq
      have h2 : B.rank ≤ Module.finrank K (Fin 0 → K) :=
        Submodule.finrank_le (R := K) (M := Fin 0 → K) _
      simp at h2
      omega
    · exact h
  have hmain := GlobalTheory.T.hermitian_self_dual_max_slope K K0 hK0 v0 hv0 n H _ hX M hlat hdual hn
  rw [← (iso_inv_dual K B A I hB).2.1]
  exact hmain

end GlobalTheory.SelfDualSlope
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muMaxDual_nonpos_of_dual_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (A : HLat K) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (e : (Fin n → K) ≃ₗ[K] A.V) (M : Submodule (𝓞 K) (Fin n → K)), A.Good → 0 < A.rank → (∀ i j, H i j ∈ K0) → (∀ (v : InfinitePlace K) (i j : Fin n), Formalism.HermitianLatticesTheory.majAt A.b A.X v (e (Pi.single i 1)) (e (Pi.single j 1)) = v.embedding (H i j)) → A.L = M.map (e.toLinearMap.restrictScalars (𝓞 K)) → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → A.muMaxDual ≤ 0 := by
  atlas_forward_decl GlobalTheory.SelfDualSlope.muMaxDual_nonpos_of_rat_coord
end

section
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lvl_consequence_one : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K), IsConjAt v0 → ∀ S : CSD K, S.Good 1 → (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) → ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r → S.ActRat r → ∀ (P : Subgroup G) (ψ : P →* Kˣ), (∀ i j, S.lvlH r P ψ i j ∈ cmMax K) ∧ (∀ v : InfinitePlace K, ((S.lvlH r P ψ).map v.embedding).PosDef) ∧ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ) ≤ S.lvlNab r P ψ := by
  intro K _ _ _ _ v0 hv0 S hS hH hpos G _ _ r hr hrat P ψ
  have hP := (Formalism.L2.DIV.level_idempotent_spec K v0 hv0 G P ψ).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ cmMax K :=
    Formalism.L2.DIV.image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (Formalism.L2.DIV.gaMat_rat S r hrat _ hP.rat)
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec :=
    (Formalism.L2.DIV.image_idempotent_spec K S.dim (S.gaMat r (lvlIdem P ψ))).1
  refine ⟨fun i j => ?_, fun v => ?_, ?_⟩
  · show ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) i j ∈ cmMax K
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine Subfield.mul_mem _ (Subfield.inv_mem _ (natCast_mem _ _)) (Subfield.sum_mem _ fun k _ => ?_)
    refine Subfield.mul_mem _ ?_ (hE k j)
    rw [Matrix.mul_apply]
    refine Subfield.sum_mem _ fun l _ => Subfield.mul_mem _ ?_ (hH l k)
    rw [Matrix.conjTranspose_apply]
    exact Formalism.L2.DIV.star_mem_cmMax (hE l i)
  · exact Formalism.L2.DIV.cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos v (hpos v)
  · intro y hy
    have h1 := Formalism.L2.DIV.level_dual_lattice_le K v0 hv0 S 1 hS (hpos v0) G r hr P ψ y hy
    rw [Nat.cast_one, one_smul] at h1
    show (S.lvlE r P ψ).mulVec y ∈ S.nabLat
    have h2 : (S.lvlE r P ψ).mulVec y ∈ S.delLat := h1
    have hle : S.delLat ≤ S.nabLat := by
      intro x hx
      simp only [CSD.delLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_comap, Submodule.mem_pi,
        Set.mem_univ, true_implies] at hx ⊢
      exact fun c => hS.del_le c (hx c)
    exact hle h2

end GlobalTheory
end

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_level_hermitian_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K), IsConjAt v0 → ∀ S : CSD K, S.Good 1 → (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) → ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r → S.ActRat r → ∀ (P : Subgroup G) (ψ : P →* Kˣ), (∀ i j, S.lvlH r P ψ i j ∈ cmMax K) ∧ (∀ v : InfinitePlace K, ((S.lvlH r P ψ).map v.embedding).PosDef) ∧ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ) ≤ S.lvlNab r P ψ := by
  atlas_forward_decl GlobalTheory.lvl_consequence_one
end

section
open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]



end GlobalTheory.Core.AmbTieStep
end
