import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.LTCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.FinExtIsClosed

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PY.LTInh

section Emb

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem emb_ext {j j' : {j : w.adicCompletion E →+* Qbar l // Continuous j}}
    (H : ∀ x : E, j.1 (algebraMap E (w.adicCompletion E) x) = j'.1 (algebraMap E (w.adicCompletion E) x)) : j = j' :=
  Subtype.ext (DFunLike.coe_injective
    ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer j.2 j'.2 (funext H)))

theorem exists_emb (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)
    {LL : FinExt l} (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) :
    ∃ j : {j : w.adicCompletion E →+* Qbar l // Continuous j}, ∀ x : E, j.1 (algebraMap E (w.adicCompletion E) x) =
      ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l) := by
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Qbar l := LL.1.val.comp τ'
  have hσ : ∀ y : ↥Bw.Kw.1, ‖σ y‖ = ‖(y : Qbar l)‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
      minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq Bw.Kw.1.val Bw.Kw.1.val.injective]
    rfl
  let τ : E →+* Qbar l :=
    σ.toRingHom.comp ((Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 fun x => Bw.j_E x)
  have hτ : ∀ x : E, ‖τ x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => hσ _
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  obtain rfl : v = w := by
    apply HeightOneSpectrum.ext
    ext y
    rw [← h y, hj.valuation_lt_one_iff, ← hτ, ← hv, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  obtain ⟨j, hc, e⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l τ v hv
  exact ⟨⟨j, hc⟩, fun x => DFunLike.congr_fun e x⟩

omit [NumberField E] in

theorem algHom_ext {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {LL : FinExt l}
    {τ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1}
    (H : ∀ x : E, τ ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ = τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩) : τ = τ' := by
  have := Bw.Kw.2
  have hd : DenseRange fun x : E => (⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥Bw.Kw.1) := fun y => by
    rw [closure_subtype, ← Set.range_comp]
    exact Bw.j_dense y.2
  exact DFunLike.coe_injective (hd.equalizer τ.toLinearMap.continuous_of_finiteDimensional
    τ'.toLinearMap.continuous_of_finiteDimensional (funext H))

end Emb

section Met

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]

variable {E Ω l} in

theorem exists_char {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (π : (w.adicCompletion E)ˣ) (hπ : IsUnifAt w π)
    (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (L₁ : FinExt l) :
    ∃ (LL : FinExt l) (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), L₁.1 ≤ LL.1 ∧ Continuous (ent ψ) ∧
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ =
        j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) ∧
      ∃ σ : Weil h, deg σ = 0 ∧ ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ ≠ 1 := by
  obtain ⟨c, hc, hcσ, -, -⟩ := GlobalTheory.LTExt.exists_lubinTate_char E Ω w A h a ha π hπ
  obtain ⟨LL, hL, -, hjL⟩ := exists_big (E := E) L₁ 1 one_pos w
  let jL : w.adicCompletion E →+* ↥LL.1 := j₀.1.codRestrict LL.1 (hjL j₀)
  let ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1 :=
    (Units.map ((Matrix.scalar (Fin 1) : ↥LL.1 →+* Matrix (Fin 1) (Fin 1) ↥LL.1).comp jL).toMonoidHom).comp c
  have hψ : ∀ g, ent ψ g = j₀.1 (c g : (w.adicCompletion E)ˣ) := fun g => by
    simp [ent, ψ, jL]
  have hW : ∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ =
      j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ)) := fun σ => by
    rw [hψ, hcσ, Units.val_mul, Units.val_zpow_eq_zpow_val]
  refine ⟨LL, ψ, hL, (j₀.2.comp hc).congr fun g => (hψ g).symm, hW, ?_⟩
  have hv : Valued.v ((1 : w.adicCompletion E) + π) = 1 := by
    apply Valuation.map_one_add_of_lt
    unfold IsUnifAt at hπ
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have h0 : (1 : w.adicCompletion E) + π ≠ 0 := fun h0 => by simp [h0] at hv
  obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 _ h0)
  have hd : deg σ = 0 := by
    have := ha.ord_eq σ
    rw [hσ, GlobalTheory.SmGL.SphCompletion.ord_completion, Units.val_mk0, hv] at this
    simpa using this.symm
  refine ⟨σ, hd, ?_⟩
  rw [hW, hd, hσ]
  simp

end Met

open Classical in

def LTCrysEmb : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
      ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
      ∀ (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (LL : FinExt l)
        (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1), Continuous (ent ψ) →
      (∀ σ : Weil h, ent ψ ⟨σ, Weil_le_Dec h σ.2⟩ = j₀.1 (((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) * ((π : w.adicCompletion E) ^ deg σ))) →
      Bw.IsCrysE P LL ψ ∧
      (∀ x ∈ Dcris (P.PD Bw.Kw) (Bw.repE LL ψ), ∃ c : ↥LL.1, (c : Qbar l) = (j₀.1 (π : w.adicCompletion E))⁻¹ ∧
            (phiVB P (LL := ↥LL.1) ^ GlobalTheory.Pst.resDeg l w) x = c • x) ∧
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL.1) (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
        (∀ x : E, j.1 (algebraMap E (w.adicCompletion E) x) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL.1) : Qbar l)) →
        ∀ n : ℤ, Bw.multE P LL ψ τ' n = if n = (if j = j₀ then -1 else 0) then 1 else 0


section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime]

theorem ent_mul {G : Type} [Group G] {LL : FinExt l} (ψ : G →* GL (Fin 1) ↥LL.1) (g g' : G) :
    ent ψ (g * g') = ent ψ g * ent ψ g' := by
  simp [ent, Matrix.mul_apply]

theorem ent_one {G : Type} [Group G] {LL : FinExt l} (ψ : G →* GL (Fin 1) ↥LL.1) : ent ψ 1 = 1 := by
  simp [ent]

theorem ent_pow {G : Type} [Group G] {LL : FinExt l} (ψ : G →* GL (Fin 1) ↥LL.1) (g : G) (n : ℕ) :
    ent ψ (g ^ n) = ent ψ g ^ n := by
  induction n with
  | zero => simp [ent_one]
  | succ n ih => rw [pow_succ, ent_mul, ih, pow_succ]

theorem norm_ent_le {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : FinExt l}
    (ψ : G →* GL (Fin 1) ↥LL.1) (hc : Continuous (ent ψ)) (g : G) : ‖ent ψ g‖ ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
  have := hC _ ⟨g ^ n, rfl⟩
  rw [ent_pow, norm_pow] at this
  linarith

theorem norm_ent {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : FinExt l}
    (ψ : G →* GL (Fin 1) ↥LL.1) (hc : Continuous (ent ψ)) (g : G) : ‖ent ψ g‖ = 1 := by
  have h1 := norm_ent_le ψ hc g
  have h2 := norm_ent_le ψ hc g⁻¹
  have h3 : ‖ent ψ g‖ * ‖ent ψ g⁻¹‖ = 1 := by rw [← norm_mul, ← ent_mul, mul_inv_cancel, ent_one, norm_one]
  nlinarith [norm_nonneg (ent ψ g), norm_nonneg (ent ψ g⁻¹)]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

open Classical in
theorem algChar_single (j₀ : {j : w.adicCompletion E →+* Qbar l // Continuous j}) (x : w.adicCompletion E) :
    algChar w (fun j => if j = j₀ then 1 else 0) x = (j₀.1 x)⁻¹ := by
  unfold algChar
  rw [finprod_eq_single _ j₀ (fun j hj => by simp [hj])]
  simp

theorem ord_unit {x : (w.adicCompletion E)ˣ} (hx : IsUnitAt w x) : GlobalTheory.SmGL.ord (w.adicCompletion E) x = 0 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold IsUnitAt at hx
  rw [hx]
  simp

theorem ord_unif_inv {x : (w.adicCompletion E)ˣ} (hx : IsUnifAt w x) :
    GlobalTheory.SmGL.ord (w.adicCompletion E) x⁻¹ = -1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold IsUnifAt at hx
  rw [Units.val_inv_eq_inv_val, map_inv₀, hx, ← WithZero.exp_neg, WithZero.log_exp]
  simp

end SlopeTestRemainingChoices

open Classical in

theorem emb_of_conrad (H : ConradLocalTied) : LTCrysEmb := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A h O _ _ _ Bw hB a ha π hπ j₀ LL ψ hc hψ
  have : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hmem : ∀ g, ent ψ g ∈ LL.1 := fun g => Subtype.property _
  have hπ0 : (π : w.adicCompletion E) ≠ 0 := π.ne_zero
  have hv : Valued.v ((1 : w.adicCompletion E) + π) = 1 := by
    apply Valuation.map_one_add_of_lt
    unfold IsUnifAt at hπ
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπL : j₀.1 (π : w.adicCompletion E) ∈ LL.1 := by
    have h0 : (1 : w.adicCompletion E) + π ≠ 0 := fun h0 => by simp [h0] at hv
    obtain ⟨σ, hσ⟩ := ha.surj (Units.mk0 _ h0)
    have hd : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [hσ, ord_unit (x := Units.mk0 _ h0) hv] at this
      omega
    have := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, hd, hσ] at this
    simp only [zpow_zero, mul_one, Units.val_mk0, map_add, map_one] at this
    simpa using LL.1.sub_mem this LL.1.one_mem
  have hall : ∀ x : (w.adicCompletion E)ˣ, j₀.1 (x : w.adicCompletion E) ∈ LL.1 := fun x => by
    obtain ⟨σ, rfl⟩ := ha.surj x
    have h1 := hmem ⟨σ, Weil_le_Dec h σ.2⟩
    rw [hψ, map_mul, map_zpow₀] at h1
    have h2 := LL.1.mul_mem h1 (LL.1.inv_mem (LL.1.toSubfield.zpow_mem hπL (deg σ)))
    have h3 : j₀.1 (π : w.adicCompletion E) ^ deg σ ≠ 0 := zpow_ne_zero _ (by simp)
    rwa [mul_inv_cancel_right₀ h3] at h2
  obtain ⟨h1, h2, h3⟩ := H E Ω l P AI hT w A h O Bw hB a ha LL ψ hc (norm_ent ψ hc)
    (fun j => if j = j₀ then 1 else 0)
    (fun x => by rw [algChar_single]; exact LL.1.inv_mem (hall x))
    (fun σ hσ => by
      have hd : deg σ = 0 := by
        have := ha.ord_eq σ
        rw [ord_unit hσ] at this
        omega
      rw [algChar_single, hψ, hd]
      simp)
  refine ⟨h1, fun x hx => ?_, fun τ' j hj n => ?_⟩
  · obtain ⟨σ, hσ⟩ := ha.surj π⁻¹
    have hd : deg σ = 1 := by
      have := ha.ord_eq σ
      rw [hσ, ord_unif_inv hπ] at this
      omega
    obtain ⟨c, hc1, hc2⟩ := h3 π σ hπ hσ x hx
    refine ⟨c, ?_, hc2⟩
    rw [hc1, algChar_single, hψ, hd, hσ]
    simp
  · rw [h2 τ' j hj n]
    by_cases hjj : j = j₀ <;> simp [hjj]

section Rat

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 ℚ)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem normV_rat (hw : w ∈ placesOver ℚ l) : normV w = l := by
  have hl : l.Prime := Fact.out
  have h1 : Ideal.absNorm w.asIdeal ∣ Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) :=
    map_dvd _ (Ideal.dvd_span_singleton.mpr hw)
  have h2 : Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l := by
    rw [Ideal.absNorm_span_singleton]
    have : ((l : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (l : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  rw [h2] at h1
  have h3 : Ideal.absNorm w.asIdeal = normV w := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [← h3]
  exact (hl.eq_one_or_self_of_dvd _ h1).resolve_left fun e => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)

theorem val_natCast {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (M : ℕ) :
    Valued.v ((M : ℕ) : v.adicCompletion E) = v.intValuation (M : 𝓞 E) := by
  have h : Valued.v (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) =
      v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e : (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) = ((M : ℕ) : v.adicCompletion E) := by
    rw [map_natCast]
    exact map_natCast (algebraMap E (v.adicCompletion E)) M
  rw [← e, h, HeightOneSpectrum.valuation_of_algebraMap]




end Rat

end GlobalTheory.PY.LTInh

end
