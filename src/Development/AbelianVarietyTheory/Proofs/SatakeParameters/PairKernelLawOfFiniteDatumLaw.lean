import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelNeQ
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.BaseHost
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

namespace GlobalTheory.BadNoConj

theorem sall_noConj_ok : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr sel S mu hX hPr hsel u hT hg
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto
  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'

end GlobalTheory.BadNoConj
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberBadPrimes_no_conjugatePair : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  first | exact @GlobalTheory.BadNoConj.sall_noConj_ok | exact GlobalTheory.BadNoConj.sall_noConj_ok | (intros; apply GlobalTheory.BadNoConj.sall_noConj_ok <;> assumption)
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.RatEqui

namespace GlobalTheory.DetStab

theorem isIntegral_det_of_stable {R E : Type} [CommRing R] [IsNoetherianRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ.det := by
  classical
  let N : Submodule R E := Submodule.span R {x | ∃ w : Fin n → L, x = (Matrix.of fun i => (w i : Fin n → E)).det}
  let M : Submodule R E := ⨆ j : Fin n, L.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hM : M.FG := Submodule.fg_iSup _ fun j => hfg.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hprod : ∀ (s : Finset (Fin n)) (f : Fin n → E), (∀ i, f i ∈ M) → ∏ i ∈ s, f i ∈ M ^ s.card := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty, pow_zero]
      exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact Submodule.mul_mem_mul (hf a) ih
  have hle : N ≤ M ^ (Finset.univ : Finset (Fin n)).card := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ (hprod _ _ fun i => ?_)
    exact Submodule.mem_iSup_of_mem i ⟨_, (w (σ i)).2, rfl⟩
  have hN : N.FG := (hM.pow _).of_le hle
  have hne : N ≠ ⊥ := by
    intro h
    have h0 : (Matrix.detRowAlternating (n := Fin n) (R := E)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : L) => (x : Fin n → E)) (fun _ => ?_) fun w => ?_
      · rw [← hsp]; congr 1; exact Subtype.range_coe
      · have : (Matrix.of fun i => (w i : Fin n → E)).det ∈ N := Submodule.subset_span ⟨w, rfl⟩
        rw [h] at this
        exact this
    have h1 := congrArg (fun f => f (1 : Matrix (Fin n) (Fin n) E)) h0
    have h2 : (1 : Matrix (Fin n) (Fin n) E).det = 0 := h1
    simp at h2
  refine isIntegral_of_smul_mem_submodule N hne hN _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => ⟨γ.mulVec (w i), hγ _ (w i).2⟩, ?_⟩
    rw [smul_eq_mul, mul_comm, ← Matrix.det_transpose γ, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem r hx

theorem prod_emb_det_eq_one (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : SD D L) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hu : γ * adj D γ = 1) (hs : ∀ v, v ∈ L ↔ γ.mulVec v ∈ L) : ∏ τ, embT D τ γ.det = 1 := by
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, -⟩ := hL
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := by
    intro x
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [Formalism.HC.HostAx.conjE_apply]
    exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : γ.det * (adj D γ).det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hadj : (adj D γ).det = D.host.conj γ.det := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ).symm
  have hz : γ.det ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar, ← hadj]
    exact ⟨by rw [mul_comm, hd], hd⟩
  have i1 := isIntegral_det_of_stable L hfg hsp γ fun v hv => (hs v).1 hv
  have i2 := isIntegral_det_of_stable L hfg hsp (adj D γ) fun v hv => (hs _).2 (by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]; exact hv)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i1
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i2
  have hspan : Submodule.span (𝓞 D.host.E) {γ.det} = Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, ha, mul_one]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨b, by rw [Algebra.smul_def, hb, mul_comm, hd]⟩
  have e1 := hχ.2 ⟨γ.det, hz⟩
  have e2 := hχ.2 1
  have e3 : ∏ τ, (embT D τ γ.det)⁻¹ = 1 := by
    have e1' : χ (Submodule.span (𝓞 D.host.E) {γ.det}) = ∏ τ, (embT D τ γ.det)⁻¹ := e1
    have e2' : χ (Submodule.span (𝓞 D.host.E) {(1 : D.host.E)}) = ∏ τ, (embT D τ 1)⁻¹ := e2
    rw [← e1', hspan, e2']
    simp
  rwa [Finset.prod_inv_distrib, inv_eq_one] at e3

end GlobalTheory.DetStab
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  first | exact @GlobalTheory.DetFields.det_of_stab | exact GlobalTheory.DetFields.det_of_stab | (intros; apply GlobalTheory.DetFields.det_of_stab <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (GlobalTheory.T.columnField_ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact GlobalTheory.T.memberBadPrimes_no_conjugatePair t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
end
end
