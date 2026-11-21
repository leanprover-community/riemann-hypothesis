import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes → ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  first | exact @GlobalTheory.GeoTie.ReadExist.exists_isReading | exact GlobalTheory.GeoTie.ReadExist.exists_isReading | (intros; apply GlobalTheory.GeoTie.ReadExist.exists_isReading <;> assumption)
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.NumPt

section Val

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

lemma vV_nonneg_of_mem (b : V) : 0 ≤ vV V (algebraMap V K b) := by
  by_cases hb : b = 0
  · subst hb; simp [vV]
  have h1 : valV V (algebraMap V K b) ≤ 1 := by
    simpa [valV] using (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one (K := K) b
  have h0 : valV V (algebraMap V K b) ≠ 0 := valV_ne_zero (by simpa using hb)
  have := (WithZero.log_le_log h0 one_ne_zero).2 h1
  simp only [vV]
  simp at this
  omega

lemma vV_one : vV V (1 : K) = 0 := by simp [vV]

lemma vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have := vV_mul (V := V) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vV_one] at this
  omega

lemma vV_eq_zero_of_mul {x y : K} (hx : x ∈ Set.range (algebraMap V K)) (hy : y ∈ Set.range (algebraMap V K))
    (h : x * y = 1) : vV V x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have ha : algebraMap V K a ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hb : algebraMap V K b ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := vV_mul (V := V) ha hb
  rw [h, vV_one] at this
  have h1 := vV_nonneg_of_mem (K := K) a
  have h2 := vV_nonneg_of_mem (K := K) b
  omega

lemma vV_irreducible {ϖ : V} (hϖ : Irreducible ϖ) : vV V (algebraMap V K ϖ) = 1 := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  simp only [vV, valV]
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ hne ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  simp

end Val

section Cmp

variable {V : Type} {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]
  {V' : Type} {K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K']
  [Algebra V' K'] [IsFractionRing V' K']

lemma exists_vV_map (ψ : K →+* K') (hψ : ∀ a : V, ψ (algebraMap V K a) ∈ Set.range (algebraMap V' K')) :
    ∃ r : ℕ, ∀ x, vV V' (ψ x) = (r : ℤ) * vV V x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨b, hb⟩ := hψ ϖ
  have hr0 : 0 ≤ vV V' (ψ (algebraMap V K ϖ)) := hb ▸ vV_nonneg_of_mem b
  refine ⟨(vV V' (ψ (algebraMap V K ϖ))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr0]
  have hint : ∀ a : V, a ≠ 0 → vV V' (ψ (algebraMap V K a)) = vV V' (ψ (algebraMap V K ϖ)) * vV V (algebraMap V K a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have hu0 : algebraMap V K (u : V) ≠ 0 := by
      simpa using u.ne_zero
    have hϖ0 : algebraMap V K ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have huK : vV V (algebraMap V K (u : V)) = 0 :=
      vV_eq_zero_of_mul ⟨_, rfl⟩ ⟨((u⁻¹ : Vˣ) : V), rfl⟩ (by rw [← map_mul]; simp)
    have huK' : vV V' (ψ (algebraMap V K (u : V))) = 0 :=
      vV_eq_zero_of_mul (hψ _) (hψ ((u⁻¹ : Vˣ) : V)) (by rw [← map_mul, ← map_mul]; simp)
    have hpow : ∀ (F : Type) [Field F] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
        [Algebra W F] [IsFractionRing W F] (y : F), y ≠ 0 → ∀ m : ℕ, vV W (y ^ m) = m * vV W y := by
      intro F _ W _ _ _ _ _ y hy m
      induction m with
      | zero => simp [vV]
      | succ m ih => rw [pow_succ, vV_mul (pow_ne_zero _ hy) hy, ih]; push_cast; ring
    rw [map_mul, map_pow, map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hϖ0),
      vV_mul ((map_ne_zero ψ).2 hu0) (pow_ne_zero _ ((map_ne_zero ψ).2 hϖ0)), huK, huK',
      hpow K V _ hϖ0, hpow K' V' _ ((map_ne_zero ψ).2 hϖ0), vV_irreducible hϖ]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb0, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb0
  have ha' : a ≠ 0 := by rintro rfl; simp at hx
  have haK : algebraMap V K a ≠ 0 := by simpa using ha'
  have hbK : algebraMap V K b ≠ 0 := by simpa using hb'
  rw [div_eq_mul_inv, map_mul, map_inv₀, vV_mul ((map_ne_zero ψ).2 haK) (inv_ne_zero ((map_ne_zero ψ).2 hbK)),
    vV_inv ((map_ne_zero ψ).2 hbK), vV_mul haK (inv_ne_zero hbK), vV_inv hbK, hint a ha', hint b hb']
  ring

end Cmp

section Main

open LocFldPf HeightOneSpectrum

theorem exists_ptC_of_finExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c →
    ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]),
      (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  intro E _ _ _ H Dw l Xo c p _ φ hIA L _ _ _ σ hσ y a n
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  haveI : NumberField L := NumberField.of_module_finite c.F L
  have hL : GlobalTheory.Reg.EvLaws Xo c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).1

  let w : HeightOneSpectrum (𝓞 L) := placeAt σ
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI : CharZero (adicCompletionIntegers L w) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (𝓞 L) (adicCompletionIntegers L w))
  obtain ⟨e1, he1, h1⟩ := exists_e (L := L) w
  let T : CDVR := { V := adicCompletionIntegers L w, cpl := isAdicComplete w }
  let ι : L →+* T.Fr := kMap w
  have hOσ : OverLa (placeAt σ) T.V ι e1 := by
    refine ⟨he1, fun x => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w x) = _
    simp only [vV, vLa]
    rw [h1, WithZero.log_pow]
    push_cast
    ring
  have hFin : T.FinRes := finite_res w

  have hlies : w.asIdeal.LiesOver (placeAt φ).asIdeal := ⟨by
    ext b
    rw [Ideal.mem_comap, mem_placeAt, mem_placeAt]
    show _ ↔ ‖σ ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L)‖ < 1
    rw [show ((algebraMap (𝓞 c.F) (𝓞 L) b : 𝓞 L) : L) = algebraMap c.F L (b : c.F) from rfl, hσ]⟩
  let io : c.F →+* T.Fr := ι.comp (algebraMap c.F L)
  have he2 : (placeAt φ).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (placeAt φ).ne_bot
  have hO : OverLa (placeAt φ) T.V io ((placeAt φ).asIdeal.ramificationIdx' w.asIdeal * e1) := by
    refine ⟨Nat.mul_pos (Nat.pos_of_ne_zero he2) he1, fun b => ?_⟩
    show vV (adicCompletionIntegers L w) (kMap w (algebraMap c.F L b)) = _
    simp only [vV, vLa]
    rw [h1, ← valuation_liesOver L (placeAt φ) w b, ← pow_mul, WithZero.log_pow]
    push_cast
    simp

  letI : Algebra c.F T.Fr := io.toAlgebra
  let ιA : L →ₐ[c.F] T.Fr := { ι with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := hL.bc L T.Fr ιA y

  obtain ⟨T', io', e', y', hO', hy'alg, φ', zz, t, hint, hmap, hbor⟩ := hIA (placeAt φ) T io _ hO hFin yT
  letI : Algebra c.F T'.Fr := io'.toAlgebra

  let ψ : T.Fr →+* T'.Fr := (φ' : T.Fr →+* T'.Fr)
  obtain ⟨r, hr⟩ := exists_vV_map (V := T.V) (V' := T'.V) ψ hint
  have hψio : ∀ b : c.F, ψ (io b) = io' b := fun b => φ'.commutes b
  have hp0 : vLa (placeAt φ) (p : c.F) ≠ 0 := by
    have hlt : (placeAt φ).valuation c.F (p : c.F) < 1 := by
      rw [show (p : c.F) = algebraMap (𝓞 c.F) c.F ((p : ℕ) : 𝓞 c.F) by simp,
        HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact natCast_mem_placeAt φ
    have hne : (placeAt φ).valuation c.F (p : c.F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    intro h0
    have : WithZero.log ((placeAt φ).valuation c.F (p : c.F)) = 0 := by
      simp only [vLa] at h0; omega
    have h2 := WithZero.exp_log hne
    rw [this, WithZero.exp_zero] at h2
    exact hlt.ne h2.symm
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have h3 := hO'.2 (p : c.F)
      rw [← hψio, hr, h0] at h3
      simp only [Nat.cast_zero, zero_mul] at h3
      have : (e' : ℤ) ≠ 0 := by exact_mod_cast hO'.1.ne'
      exact (mul_ne_zero this hp0) h3.symm
    · exact h0
  have hOσ' : OverLa (placeAt σ) T'.V (ψ.comp ι) (r * e1) := hOσ.bc ψ hrpos hr

  obtain ⟨k', hk'⟩ := GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue p L σ T' (ψ.comp ι) (r * e1) hOσ' hy'alg
  have hk : IsReading φ T' io' k' := by
    refine ⟨fun b => ?_, hk'.int⟩
    rw [← hψio, ← hσ b]
    exact hk'.comp (algebraMap c.F L b)

  obtain ⟨z₀, hz₀⟩ := PtC.exists_of_reading hk y' hy'alg
  refine ⟨z₀, k' (wchar (ex Dw a n) t), ?_, fun f hf => ?_⟩
  · rw [map_ne_zero]
    simp [wchar, Finset.prod_ne_zero_iff]
  · rw [hz₀ a n f hf]
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test L y
    have e1' : evR Xo c f y = χ (f q y₀) := GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ y hy₀
    have e2 : evR Xo c f zz = (φ'.comp (ιA.comp χ)) (f q y₀) :=
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q _ y₀ zz
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ φ' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ ιA hy₀ hyT) hmap)
    have e3 : evI y' f = wchar (ex Dw a n) t * evR Xo c f zz :=
      hL.wt a n f hf T'.Fr t zz y'.1 (hL.test _ _) (hL.test _ _) hbor
    rw [e3, map_mul, e2, e1']
    congr 1
    exact hk'.comp (χ (f q y₀))

end Main

end GlobalTheory.GeoTie.NumPt
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c → ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]), (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  atlas_forward_decl GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 200000 in

theorem sec_eq_zero_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  intro E _ _ _ H Dw l Xo c a n h hh hv
  obtain ⟨hL, -, -, -⟩ := evLaws_genFr_nonempty_comp E H Dw l Xo c
  funext p y
  show h p y = 0

  have key : ∀ m : Ideal p.R, m.IsMaximal → h p y ∈ m := by
    intro m hm
    letI : Field (p.R ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType c.F (p.R ⧸ m) := inferInstance
    haveI : FiniteDimensional c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F (p.R ⧸ m)
    obtain ⟨w, hw⟩ := hL.bc p.R (p.R ⧸ m) (Ideal.Quotient.mkₐ c.F m) y
    have e := evR_eq_map_of_test_point hL hh p (Ideal.Quotient.mkₐ c.F m) y w hw
    rw [hv (p.R ⧸ m) w, Ideal.Quotient.mkₐ_eq_mk] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp e.symm

  have hj : h p y ∈ (⊥ : Ideal p.R).jacobson :=
    Ideal.mem_sInf.mpr fun J hJ => key J hJ.2
  have hrad : (⊥ : Ideal p.R).IsRadical := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact p.rad ⟨k, hk⟩
  rw [IsJacobsonRing.out (inferInstance : IsJacobsonRing p.R) hrad] at hj
  exact hj

end GlobalTheory.Reg
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  atlas_forward_decl GlobalTheory.Reg.sec_eq_zero_of_finite_values
end

section
section
namespace GlobalTheory

open Module in

theorem eq_zero_of_sum_mul_embeddings_eq_zero (F Ω L : Type) [Field F] [CharZero F] [Field Ω]
    [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ)
    (e : Fin m → Ω) (he : LinearIndependent F e) (_halg : ∀ t, IsAlgebraic F (e t))
    (a : Fin m → L) (h : ∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F L
  let ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])
  let E := Algebra.embeddingsMatrixReindex F Ω b ε
  have hE : E.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε
    rw [show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)
  have hEa : ∀ i k, E i k = ε k (b i) := by
    intro i k
    simp [E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  let v : Fin (Module.finrank F L) → Ω := fun i => ∑ t, (b.repr (a t) i) • e t
  have hv : Matrix.vecMul v E = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct]
    simp only [Pi.zero_apply, hEa, v]
    have hk := h (ε k)
    rw [← hk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hE hv
  have hc : ∀ t i, b.repr (a t) i = 0 := by
    intro t i
    have := congrFun hv0 i
    exact (Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t
  funext t
  rw [Pi.zero_apply, ← b.sum_repr (a t)]
  simp [hc]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' : ∀ (F Ω L : Type) [Field F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ) (e : Fin m → Ω), LinearIndependent F e → (∀ t, IsAlgebraic F (e t)) → ∀ a : Fin m → L, (∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) → a = 0 := by
  atlas_forward_decl GlobalTheory.eq_zero_of_sum_mul_embeddings_eq_zero
end

section
namespace GlobalTheory

theorem linRelation_descend : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι]
    (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) →
    ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  intro K Ω _ _ _ ι _ V c hc hV
  obtain ⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  let b := Module.Basis.ofVectorSpace K Ω
  obtain ⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs0
    have h0 : b.repr (c s0) = 0 := Finsupp.ext h
    exact b.repr.map_eq_zero_iff.mp h0
  refine ⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩
  have h2 : ∑ s, v s • c s = 0 := by
    rw [← hV v hv]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h3 := congrArg (fun x => b.repr x j) h2
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory

alias _root_.GlobalTheory.T.exists_linear_relation_descend_base_field := _root_.GlobalTheory.linRelation_descend
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

namespace GlobalTheory.PointsDetectAlg

theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (hI : IntAll Xo c)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {ι : Type} [Fintype ι] (g : ι → Rul Xo c) (hg : ∀ s, g s ∈ sec Xo c a n)
    (hli : LinearIndependent c.F g) (w : ι → ℂ_[p])
    (hw : ∀ z : PtC Xo c φ, ∑ s, w s * valC z.1 (g s) = 0) : w = 0 := by
  by_contra hw0
  let wP : ι → PAt φ := w
  have hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    obtain ⟨z, u, hu, hz⟩ := GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom)
      (fun a => by simp [toCp_algebraMap]) y a n
    have h1 := hw z
    simp only [hz _ (hg _)] at h1
    have h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      change u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))
      ring
    exact (mul_eq_zero.1 h2).resolve_left hu
  let K := algebraicClosure c.F (PAt φ)
  let V : Set (ι → K) := {v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L)
    (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_linear_relation_descend_base_field K (PAt φ) ι V wP hw0 (by
    rintro v ⟨L, _, _, _, σ, y, hv⟩
    simpa only [IntermediateField.algebraMap_apply, hv] using hrel L σ y)

  have hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    have hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V :=
      ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩
    have := congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)
    simpa using this

  let K0 := IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))
  have hfin : FiniteDimensional c.F K0 := IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact (mem_algebraicClosure_iff.1 (d s).2).isIntegral)
  let bs := Module.finBasis c.F K0
  let m := Module.finrank c.F K0
  let e : Fin m → PAt φ := fun t => (bs t : PAt φ)
  have he : LinearIndependent c.F e :=
    bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)
  have hea : ∀ t, IsAlgebraic c.F (e t) := fun t =>
    (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val
  have dmem : ∀ s, (d s : PAt φ) ∈ K0 := fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩
  let q : ι → Fin m → c.F := fun s t => bs.repr ⟨d s, dmem s⟩ t
  have hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t := by
    intro s
    have h := congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)
    simp only [IntermediateField.coe_sum, Algebra.smul_def] at h
    exact h.symm
  let hh : Fin m → Rul Xo c := fun t => ∑ s, q s t • g s
  have hhsec : ∀ t, hh t ∈ sec Xo c a n := fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)
  have hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m),
      evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y := by
    intro L _ _ y t
    have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
      (fun s => q s t • g s) Finset.univ
    simp only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this
    exact this
  have hzero : ∀ t, hh t = 0 := by
    intro t
    refine GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_
    have := GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by
      rw [← hdrel L σ y]
      simp only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    exact congrFun this t
  have hq0 : ∀ s t, q s t = 0 := fun s t =>
    Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s
  apply hd0
  funext s
  apply Subtype.ext
  rw [hq s]
  simp [hq0]

end GlobalTheory.PointsDetectAlg

namespace GlobalTheory.PointsDetectAlg

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

theorem detects : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), Detects YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx
  let bV := Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))
  let B := Algebra.TensorProduct.basis (NX.KB S i b) bV
  let r := B.repr x
  let g : r.support → T0.R ((j : ℕ) + 1) := fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))
  have hx' : x = ∑ s : r.support, r s • B s := by
    conv_lhs => rw [← B.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_coe_sort r.support (fun s => r s • B s)).symm
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0 := by
    intro z
    have h := hx z
    rw [hx'] at h
    have e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s) :=
      map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ
    rw [← h]
    refine Eq.trans ?_ e.symm
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm
    congr 1
    have hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _) :=
      Algebra.TensorProduct.basis_apply _ _
    refine Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm
    refine Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm
    exact (one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)
  have hli : LinearIndependent T0.Q.c.F g := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf s
    have h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0 := by
      rw [← hcf, map_sum]
      simp only [cuspOf_smul, RingEquiv.apply_symm_apply]
      push_cast
      rfl
    have h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0 :=
      (cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)
    have h3 := Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s
    simpa using h3
  have hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩
  have hw := core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli
    (fun s => iC (r s)) hval
  have hr : ∀ s : r.support, r s = 0 := fun s => (map_eq_zero iC).1 (congrFun hw s)
  rw [hx']
  exact (Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl

end GlobalTheory.PointsDetectAlg

end
end
