import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

namespace GlobalTheory.HTLat.Point

theorem smul_latTQuot_le_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C) {n : ℕ} (r : Fin n → O) (a : Fin n → 𝓞 E), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then d else 0) → ∀ {w : P.V}, w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ → d • w ∈ P.latT := by
  intro p _ C _ _ _ _ O _ _ _ _ _ E _ _ _ P φ d n r a hsum w hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hact : ∀ (b : 𝓞 E) (x : P.V), x ∈ P.latT → P.actV b x ∈ P.latT := by
    intro b x hx
    obtain ⟨s, rfl⟩ := hx
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | tmul c t => exact ⟨c ⊗ₜ P.actT b t, by rw [P.inclT_tmul, P.inclT_tmul]; rfl⟩
  have e : d • idem (isSplitting_embO P.integers) φ =
      ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := (isSplitting_embO P.integers).1 (by
    ext ψ
    rw [map_smul, splitMap_idem, map_sum, Finset.sum_apply]
    simp only [splitMap_tmul, RingHom.comp_apply, algebraMap_embO, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    rw [hsum ψ]
    split_ifs <;> simp)
  change d • proj (isSplitting_embO P.integers) P.actV φ y ∈ P.latT
  rw [proj, ← LinearMap.smul_apply, ← map_smul, e, map_sum, LinearMap.sum_apply]
  refine P.latT.sum_mem fun k _ => ?_
  rw [tensorAction_tmul, algebraMap_smul]
  exact P.latT.smul_mem _ (hact _ _ hy)

end GlobalTheory.HTLat.Point
end

section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem exists_aut (φ₀ φ : E →+* C) : ∃ g : E ≃ₐ[ℚ] E, φ = φ₀.comp g.toRingHom := by
  let K := AlgebraicClosure C
  let ι := algebraMap C K
  let F : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K) := fun g => ((ι.comp φ₀).comp g.toRingHom).toRatAlgHom
  have hF : Function.Injective F := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] K => f x) hgh
    simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact φ₀.injective (ι.injective this)
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hF, ?_⟩
    rw [AlgHom.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  obtain ⟨g, hg⟩ := hbij.2 ((ι.comp φ).toRatAlgHom)
  refine ⟨g, ?_⟩
  ext x
  have := congrArg (fun f : E →ₐ[ℚ] K => f x) hg
  simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
  exact (ι.injective this).symm

theorem sum_aut_eq_trace (φ₀ : E →+* C) (x : E) :
    ∑ g : E ≃ₐ[ℚ] E, φ₀ (g x) = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  have h := GlobalTheory.ColengthDifferent.sum_eq_trace (fun g : E ≃ₐ[ℚ] E => φ₀.comp g.toRingHom) ?_
    (by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]) x
  · simpa using h
  · intro g h hgh
    ext y
    exact φ₀.injective (RingHom.congr_fun hgh y)

theorem comp_eq_iff (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) : φ₀.comp h.toRingHom = φ₀ ↔ h = 1 := by
  constructor
  · intro hh
    ext x
    exact φ₀.injective (RingHom.congr_fun hh x)
  · rintro rfl
    ext x
    rfl

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem map_expand (φ₀ : E →+* C) (x : E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * algebraMap ℚ C (Algebra.trace ℚ E (integralBasis E k * x)) = φ₀ x := by
  set b := integralBasis E
  conv_rhs => rw [← b.traceDual.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul φ₀, mul_comm x (b k),
    mul_comm (φ₀ (b.traceDual k))]
  congr 1
  exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ C) (φ₀.comp (algebraMap ℚ E))) _

theorem orth_aut (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * φ₀ (h (integralBasis E k)) = if h = 1 then 1 else 0 := by
  set b := integralBasis E
  let f : (E ≃ₐ[ℚ] E) → (E →* C) := fun g => (φ₀.comp g.toRingHom).toMonoidHom
  have hf : Function.Injective f := by
    intro g g' hgg
    ext y
    exact φ₀.injective (DFunLike.congr_fun hgg y)
  have li := (linearIndependent_monoidHom E C).comp f hf
  let c : (E ≃ₐ[ℚ] E) → C := fun g =>
    (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k))) - if g = 1 then 1 else 0
  have hc : ∑ g, c g • ((fun f : E →* C => (f : E → C)) ∘ f) g = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, f,
      MonoidHom.coe_coe, RingHom.coe_comp, RingHom.toMonoidHom_eq_coe]
    have e1 : ∀ g : E ≃ₐ[ℚ] E, c g * φ₀ (g x) =
        (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k * x))) - (if g = 1 then φ₀ x else 0) := by
      intro g
      simp only [c, sub_mul, Finset.sum_mul, map_mul, mul_assoc]
      split_ifs with hg
      · subst hg; simp
      · simp
    show ∑ g, c g * φ₀ (g x) = 0
    rw [Finset.sum_congr rfl fun g _ => e1 g, Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_aut_eq_trace φ₀]
    rw [map_expand φ₀ x]
    simp
  have := Fintype.linearIndependent_iff.mp li c hc h
  simp only [c, sub_eq_zero] at this
  exact this

theorem orth (φ₀ σ : E →+* C) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * σ (integralBasis E k) = if σ = φ₀ then 1 else 0 := by
  obtain ⟨h, rfl⟩ := exists_aut φ₀ σ
  have := orth_aut φ₀ h
  rw [comp_eq_iff]
  exact this

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem trace_mul_traceDual (a : 𝓞 E) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E ((a : E) * (integralBasis E).traceDual k) =
      (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) := by
  have h := ((integralBasis E).traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E a) k
  rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply] at h
  rw [← eq_intCast (algebraMap ℤ ℚ), h]

theorem base {O : Type} [CommRing O] [Algebra O C] {v : Valuation C ℝ≥0} (hv : v.Integers O)
    (φ₀ : E →+* C) :
    ∃ δ : C, δ ≠ 0 ∧ (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then δ else 0) ∧
    ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then s else 0) → v s ≤ v δ := by
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := (integralBasis E).index_nonempty
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ
    (fun k => v (φ₀ ((integralBasis E).traceDual k))) Finset.univ_nonempty
  have hy : φ₀ ((integralBasis E).traceDual k₀) ≠ 0 :=
    (map_ne_zero φ₀).2 ((integralBasis E).traceDual.ne_zero k₀)
  have hvy : v (φ₀ ((integralBasis E).traceDual k₀)) ≠ 0 := (Valuation.ne_zero_iff v).2 hy
  refine ⟨(φ₀ ((integralBasis E).traceDual k₀))⁻¹, inv_ne_zero hy, ?_, ?_⟩
  · have hr : ∀ k, ∃ o : O, algebraMap O C o =
        (φ₀ ((integralBasis E).traceDual k₀))⁻¹ * φ₀ ((integralBasis E).traceDual k) := by
      intro k
      apply hv.exists_of_le_one
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (pos_iff_ne_zero.2 hvy), mul_one]
      exact hk₀ k (Finset.mem_univ _)
    choose r hr using hr
    let e := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
    refine ⟨Fintype.card _, fun i => r (e.symm i), fun i => RingOfIntegers.basis E (e.symm i),
      fun σ => ?_⟩
    rw [Equiv.sum_comp e.symm (fun k => algebraMap O C (r k) * σ (RingOfIntegers.basis E k))]
    have h2 : ∀ k, σ (RingOfIntegers.basis E k : E) = σ (integralBasis E k) := by
      intro k
      rw [integralBasis_apply]
    simp_rw [hr, h2, mul_assoc, ← Finset.mul_sum]
    rw [orth φ₀ σ]
    split_ifs <;> simp
  · intro n r a s hs
    have h1 : ∀ g : E ≃ₐ[ℚ] E, ∑ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
        if g = 1 then s * φ₀ ((integralBasis E).traceDual k₀) else 0 := by
      intro g
      have := hs (φ₀.comp g.toRingHom)
      rw [comp_eq_iff] at this
      have e3 : ∀ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
          (algebraMap O C (r k) * φ₀ (g (a k))) * φ₀ (g ((integralBasis E).traceDual k₀)) := by
        intro k
        rw [map_mul, map_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun k _ => e3 k, ← Finset.sum_mul]
      erw [this]
      split_ifs with hg
      · subst hg; rfl
      · simp
    have h2 := Finset.sum_congr rfl fun g (_ : g ∈ (Finset.univ : Finset (E ≃ₐ[ℚ] E))) => h1 g
    rw [Finset.sum_comm] at h2
    simp_rw [← Finset.mul_sum, sum_aut_eq_trace φ₀, trace_mul_traceDual] at h2
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have hle : v (s * φ₀ ((integralBasis E).traceDual k₀)) ≤ 1 := by
      rw [← h2]
      have : ∑ k, algebraMap O C (r k) * algebraMap ℚ C (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : ℚ) =
          algebraMap O C (∑ k, r k * (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : O)) := by
        simp [map_sum, map_mul, map_intCast]
      rw [this]
      exact hv.map_le_one _
    calc v s = v (s * φ₀ ((integralBasis E).traceDual k₀)) * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by
          rw [← map_mul, mul_assoc, mul_inv_cancel₀ hy, mul_one]
      _ ≤ 1 * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by gcongr
      _ = v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := one_mul _

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

theorem indicator_inverseDifferent : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  intro E _ _ _ C _ _ v O _ _ hv
  by_cases hne : Nonempty (E →+* C)
  swap
  · exact ⟨1, one_ne_zero, fun φ => (hne ⟨φ⟩).elim⟩
  obtain ⟨φ₀⟩ := hne
  obtain ⟨δ, hδ0, ha, hb⟩ := base hv φ₀
  refine ⟨δ, hδ0, fun φ => ?_⟩
  obtain ⟨g, rfl⟩ := exists_aut φ₀ φ
  constructor
  · obtain ⟨n, r, a, h⟩ := ha
    refine ⟨n, r, fun k => RingOfIntegers.mapRingHom g.symm.toRingHom (a k), fun σ => ?_⟩
    have hσ := h (σ.comp g.symm.toRingHom)
    have e1 : σ.comp g.symm.toRingHom = φ₀ ↔ σ = φ₀.comp g.toRingHom := by
      constructor
      · rintro rfl
        ext x
        simp
      · rintro rfl
        ext x
        simp
    rw [if_congr e1 rfl rfl] at hσ
    rw [← hσ]
    rfl
  · intro n r a s hs
    apply hb n r (fun k => RingOfIntegers.mapRingHom g.toRingHom (a k)) s
    intro τ
    have hτ := hs (τ.comp g.toRingHom)
    have e1 : τ.comp g.toRingHom = φ₀.comp g.toRingHom ↔ τ = φ₀ := by
      constructor
      · intro hh
        ext x
        have := RingHom.congr_fun hh (g.symm x)
        simpa using this
      · rintro rfl
        rfl
    rw [if_congr e1 rfl rfl] at hτ
    rw [← hτ]
    rfl

end GlobalTheory.InvDifferentArith
end

section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_trace_separating_element : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  first | exact @GlobalTheory.InvDifferentArith.indicator_inverseDifferent | exact GlobalTheory.InvDifferentArith.indicator_inverseDifferent | (intros; apply GlobalTheory.InvDifferentArith.indicator_inverseDifferent <;> assumption)
end

section
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.TateLocFree

theorem exists_place_decomp : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  intro p _ C _ _ _ v O _ _ _ E _ _ _ P φ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (embO P.integers φ)
  obtain ⟨hdom, hpid, -⟩ := GlobalTheory.PlaceMono.place_monogenic p (𝓞 E) w
  let A := ℤ_[p] ⊗[ℤ] 𝓞 E
  let e : A := w.e
  let I : Ideal A := Ideal.span {1 - e}
  letI : Module A P.T := Module.compHom P.T (tensorAction P.actT).toRingHom
  have hsmul : ∀ (a : A) (t : P.T), a • t = tensorAction P.actT a t := fun _ _ => rfl
  haveI : IsScalarTower ℤ_[p] A P.T := ⟨fun c a t => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  let M : Submodule A P.T := LinearMap.range (LinearMap.lsmul A P.T e)
  have hee : e * e = e := w.idem
  have hfix : ∀ m ∈ M, e • m = m := by
    rintro _ ⟨t, rfl⟩
    change e • e • t = e • t
    rw [smul_smul, hee]
  have htor : Module.IsTorsionBySet A M I := by
    intro x a
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 a.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← hc, mul_smul, sub_smul, one_smul, hfix _ x.2, sub_self, smul_zero,
      Submodule.coe_zero]
  letI : Module (A ⧸ I) M := htor.module
  haveI : IsScalarTower A (A ⧸ I) M := htor.isScalarTower
  haveI : IsDomain (A ⧸ I) := hdom
  haveI : IsPrincipalIdealRing (A ⧸ I) := hpid
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[p] A
  haveI : Module.Finite A P.T := Module.Finite.of_restrictScalars_finite ℤ_[p] A P.T
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite A (A ⧸ I) M
  haveI : Module.Finite ℤ_[p] (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] I)
  haveI : Module.IsTorsionFree (A ⧸ I) M := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[p]) hr
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hc)
    have h1 : (algebraMap ℤ_[p] A c) • (m : P.T) = 0 := by
      have : (algebraMap ℤ_[p] (A ⧸ I) c) • m = 0 := by rw [← hs, mul_smul, h, smul_zero]
      have h2 : (((algebraMap ℤ_[p] (A ⧸ I) c) • m : M) : P.T) = 0 := by rw [this]; rfl
      exact h2
    rw [algebraMap_smul] at h1
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left hc0
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A ⧸ I) (M := M)
  have hI : (I : Submodule A A) ≤ LinearMap.ker (LinearMap.mulLeft A e) := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
    linear_combination c * (1 - hee)
  let liftE : (A ⧸ I) →ₗ[A] A := Submodule.liftQ I (LinearMap.mulLeft A e) hI
  have hlift : ∀ (r : A ⧸ I) (m : M), liftE r • (m : P.T) = ((r • m : M) : P.T) := by
    intro r m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : liftE (Ideal.Quotient.mk I x) = e * x := Submodule.liftQ_apply _ _ _
    rw [h1, mul_comm, mul_smul, hfix _ m.2]
    rfl
  let emap : P.T →ₗ[A] M := (LinearMap.lsmul A P.T e).rangeRestrict
  let L : Fin n → (P.T →ₗ[A] A) := fun j => liftE ∘ₗ ((b.coord j).restrictScalars A) ∘ₗ emap
  refine ⟨n, fun j => (b j : P.T), fun j => (L j).restrictScalars ℤ_[p], e, ?_, hw, ?_⟩
  · intro j a t
    have h1 : P.actT a t = (1 ⊗ₜ a : A) • t := by
      rw [hsmul, tensorAction_tmul, one_smul]
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, h1, map_smul, smul_eq_mul]
  · intro t
    have h0 : ((emap t : M) : P.T) = e • t := rfl
    rw [← hsmul, ← h0, ← b.sum_repr (emap t), Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsmul, ← hlift]
    rfl
end GlobalTheory.TateLocFree
end

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_linear_functional_cm : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  atlas_forward_decl GlobalTheory.TateLocFree.exists_place_decomp
end

section
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EigGlue

section Alg

variable {O R ι : Type} [CommRing O] [Field R] [DecidableEq ι] {σ : ι → O →+* R}

theorem eq_smul_idem (h : IsSplitting σ) (i : ι) (z : R ⊗[ℤ] O)
    (hz : ∀ a, (1 ⊗ₜ a) * z = σ i a • z) : z = splitMap σ z i • idem h i := by
  apply h.1
  funext k
  rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, mul_zero]
    have hne : σ k ≠ σ i := fun e => hk (h.injective e)
    obtain ⟨a, ha⟩ : ∃ a, σ k a ≠ σ i a := by
      by_contra hc
      push Not at hc
      exact hne (RingHom.ext hc)
    have e := congrArg (fun t => splitMap σ t k) (hz a)
    simp only [map_mul, Pi.mul_apply, splitMap_tmul, one_mul, map_smul, Pi.smul_apply, smul_eq_mul] at e
    have : (σ k a - σ i a) * splitMap σ z k = 0 := by rw [sub_mul, e, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)

end Alg

section Act

variable {p : ℕ} [Fact p.Prime] (C : Type) [Field C] [Algebra ℤ_[p] C] {E : Type} [Field E]
  {T : Type} [AddCommGroup T] [Module ℤ_[p] T] (ρ : 𝓞 E →+* Module.End ℤ_[p] T)

def inclC : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] C ⊗[ℤ] 𝓞 E :=
  Algebra.TensorProduct.map (Algebra.ofId ℤ_[p] C) (AlgHom.id ℤ (𝓞 E))

theorem inclC_tmul (r : ℤ_[p]) (a : 𝓞 E) : inclC C (r ⊗ₜ a) = algebraMap ℤ_[p] C r ⊗ₜ a := by
  simp [inclC, Algebra.ofId_apply]

theorem tensorAction_inclC (z : ℤ_[p] ⊗[ℤ] 𝓞 E) (x : C ⊗[ℤ_[p]] T) :
    tensorAction (baseChangeAction C ρ) (inclC C z) x = (tensorAction ρ z).baseChange C x := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, LinearMap.baseChange_add]
  | tmul r a =>
    have e : tensorAction ρ (r ⊗ₜ a) = r • ρ a := LinearMap.ext fun y => by
      rw [tensorAction_tmul, LinearMap.smul_apply]
    rw [inclC_tmul, tensorAction_tmul, e, LinearMap.baseChange_smul,
      LinearMap.smul_apply, algebraMap_smul, baseChangeAction_apply]

variable {m : ℕ} (ℓ : Fin m → (T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E))

def coordC (j : Fin m) : C ⊗[ℤ_[p]] T →ₗ[C] C ⊗[ℤ] 𝓞 E :=
  ((inclC C).toLinearMap ∘ₗ ℓ j).liftBaseChange C

theorem coordC_tmul (j : Fin m) (c : C) (t : T) : coordC C ℓ j (c ⊗ₜ t) = c • inclC C (ℓ j t) := by
  rw [coordC, LinearMap.liftBaseChange_tmul]
  rfl

variable {ρ ℓ}

theorem coordC_act (hℓ : ∀ j a t, ℓ j (ρ a t) = (1 ⊗ₜ a) * ℓ j t) (j : Fin m) (a : 𝓞 E)
    (x : C ⊗[ℤ_[p]] T) : coordC C ℓ j (baseChangeAction C ρ a x) = (1 ⊗ₜ a) * coordC C ℓ j x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul c t =>
    rw [baseChangeAction_apply, LinearMap.baseChange_tmul, coordC_tmul, coordC_tmul, hℓ, map_mul,
      mul_smul_comm]
    congr 2
    simp [inclC]

theorem baseChange_eq_sum {u : Fin m → T} {e : ℤ_[p] ⊗[ℤ] 𝓞 E}
    (hE : ∀ t, tensorAction ρ e t = ∑ j, tensorAction ρ (ℓ j t) (u j)) (x : C ⊗[ℤ_[p]] T) :
    (tensorAction ρ e).baseChange C x =
      ∑ j, tensorAction (baseChangeAction C ρ) (coordC C ℓ j x) (1 ⊗ₜ u j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_apply, Finset.sum_add_distrib]
  | tmul c t =>
    rw [LinearMap.baseChange_tmul, hE, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordC_tmul, map_smul, LinearMap.smul_apply, tensorAction_inclC, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Act

section Point

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E]

theorem splitMap_inclC (hv : v.Integers O) (φ : E →+* C) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    splitMap (fun ψ : E →+* C => (algebraMap O C).comp (embO hv ψ)) (inclC C e) φ =
      algebraMap O C (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO hv φ) e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul r a =>
    rw [inclC_tmul, splitMap_tmul]
    simp [ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt, Algebra.ofId_apply, IsScalarTower.algebraMap_apply ℤ_[p] O C]

def intPart (O C E : Type) [CommRing O] [Field C] [Algebra O C] [Field E] :
    Submodule O (C ⊗[ℤ] 𝓞 E) :=
  Submodule.span O (Set.range fun a : 𝓞 E => (1 : C) ⊗ₜ[ℤ] a)

theorem inclC_mem_intPart (z : ℤ_[p] ⊗[ℤ] 𝓞 E) : inclC C z ∈ intPart O C E := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul r a =>
    rw [inclC_tmul, IsScalarTower.algebraMap_apply ℤ_[p] O C, ← mul_one (algebraMap O C _),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem exists_fin_of_mem_intPart {z : C ⊗[ℤ] 𝓞 E} (hz : z ∈ intPart O C E) :
    ∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), z = ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := by
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hz
  refine ⟨n, f, fun k => (g k).2.choose, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (g k).2.choose_spec, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

end Point

theorem mem_latTQuot_of_smul_mem_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  intro p _ C _ _ _ v O _ _ _ _ _ E _ _ _ P φ d hd hδ m u ℓ e hℓ he hE w hw hdw
  let σf : (E →+* C) → 𝓞 E →+* C := fun ψ => (algebraMap O C).comp (embO P.integers ψ)
  have h : IsSplitting σf := isSplitting_embO P.integers
  have hyV : d • w ∈ eigenSub P.actV (σf φ) := Submodule.smul_mem _ d hw
  have hact : P.actV = baseChangeAction C P.actT := rfl

  have h1 : (tensorAction P.actT e).baseChange C (d • w) = d • w := by
    rw [← tensorAction_inclC, ← hact, tensorAction_of_mem (σ := σf) (i := φ) hyV,
      splitMap_inclC P.integers φ e, he, map_one, one_smul]

  have h2 : ∀ j, ∃ o : O, coordC C ℓ j (d • w) = (d * algebraMap O C o) • idem h φ := by
    intro j
    have hz : ∀ a, (1 ⊗ₜ a) * coordC C ℓ j (d • w) = σf φ a • coordC C ℓ j (d • w) := by
      intro a
      rw [← coordC_act C hℓ, ← hact, mem_eigenSub.1 hyV a, map_smul]
    have heq := eq_smul_idem h φ _ hz
    set s := splitMap σf (coordC C ℓ j (d • w)) φ with hs
    have hmem : coordC C ℓ j (d • w) ∈ intPart O C E := by
      obtain ⟨x, hx⟩ := hdw
      rw [← hx]
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
      | tmul c t =>
        rw [Point.inclT_tmul, coordC_tmul, algebraMap_smul]
        exact Submodule.smul_mem _ _ (inclC_mem_intPart _)
    obtain ⟨n, r, a, hra⟩ := exists_fin_of_mem_intPart hmem
    have hvs : v s ≤ v d := by
      refine hδ n r a s fun ψ => ?_
      have e1 : splitMap σf (coordC C ℓ j (d • w)) ψ = s * (Pi.single φ 1 : (E →+* C) → C) ψ := by
        conv_lhs => rw [heq]
        rw [map_smul, splitMap_idem, Pi.smul_apply, smul_eq_mul]
      have e2 : splitMap σf (coordC C ℓ j (d • w)) ψ =
          ∑ k, algebraMap O C (r k) * ψ (a k) := by
        rw [hra, map_sum, Finset.sum_apply]
        simp only [splitMap_tmul, σf, RingHom.comp_apply, algebraMap_embO]
      rw [← e2, e1]
      by_cases hψ : ψ = φ
      · subst hψ; simp
      · simp [hψ]
    have hvd : v (s * d⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ hvs zero_le
    obtain ⟨o, ho⟩ := P.integers.exists_of_le_one hvd
    refine ⟨o, ?_⟩
    rw [heq, ho, mul_comm s, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  choose o ho using h2

  have h3 : d • w = d • proj h P.actV φ (∑ j, o j • ((1 : C) ⊗ₜ[ℤ_[p]] u j)) := by
    conv_lhs => rw [← h1, baseChange_eq_sum C hE]
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho, ← hact, map_smul, LinearMap.smul_apply, ← proj, ← algebraMap_smul C (o j), map_smul,
      smul_smul]
  have hw' := smul_right_injective _ hd h3
  refine (mem_eigQuotLat _ _).2 ⟨_, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (P.one_tmul_mem_latT _), hw'.symm⟩

end GlobalTheory.EigGlue
end
end

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_trace_dual : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  atlas_forward_decl GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

noncomputable section

namespace GlobalTheory.EigDiff

theorem eigSt_holds : EigSt := by
  intro E _ _ _ _ H p _
  have hv : (Valued.v : Valuation ℂ_[p] ℝ≥0).Integers 𝓞_ℂ_[p] := Valuation.valuationSubring.integers _
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.idempotent_trace_separating_element E ℂ_[p] Valued.v 𝓞_ℂ_[p] hv
  refine ⟨δ, hδ0, ?_⟩
  intro l c _ _ Q τ w hw
  rw [htLat_psi]
  obtain ⟨⟨n, r, a, hsum⟩, hb⟩ := hδ (embAt c ℂ_[p] τ.1)
  constructor
  · intro h
    exact GlobalTheory.HTLat.Point.smul_latTQuot_le_latT Q _ δ r a hsum h
  · intro h
    obtain ⟨m, u, ℓ, e, h1, h2, h3⟩ := GlobalTheory.T.p_adic_point_linear_functional_cm Q (embAt c ℂ_[p] τ.1)
    exact GlobalTheory.T.p_adic_point_trace_dual Q _ δ hδ0 hb m u ℓ e h1 h2 h3 w hw h

end GlobalTheory.EigDiff
end
end

open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.EigenvalueStatement : EigSt := by
  atlas_forward_decl GlobalTheory.EigDiff.eigSt_holds
end
