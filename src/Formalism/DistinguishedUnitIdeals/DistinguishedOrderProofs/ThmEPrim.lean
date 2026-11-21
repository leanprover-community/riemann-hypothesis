import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusCoboundedArc
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GoodOf
import Formalism.DistinguishedUnitIdeals.WordConsts
import Formalism.DistinguishedUnitIdeals.FinalE
import Formalism.DistinguishedUnitIdeals.DescentLemmasAllHold
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.ArcLiftOfLocalizationData
import Formalism.DistinguishedUnitIdeals.LemmaCFull
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LinExtEqZeroOfMemExt
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.LevelsModConstIffOfNoDown

section
namespace Formalism.ExponentWindows.E.Full

open PowerSeries

theorem constLift_of_word {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {ℓ ell r₁ r₂ a₀ rr : ℕ} {p : ℕ → PowerSeries O} {H b : ℕ → ℕ}
    {kind : ℕ → Kind} {U₁ : ℕ → Submodule O (Fin r₁ → O)} {U₂ : ℕ → Submodule O (Fin r₂ → O)}
    {prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)}
    (hS : LevelModelSetting ϖ ℓ ell p H b kind U₁ U₂) (hL : LLift ℓ rr prL) (hr : rr ≤ 2 * a₀)
    (hW : ArcWord ϖ ℓ ell a₀ p b kind U₁ U₂ prL) :
    ConstLift ϖ ℓ p H b kind U₁ U₂ ell a₀ prL := by
  obtain ⟨cN, cD, cDU, cDD, cUD⟩ := CL.lifts_mod_const_of_words
  rcases hW with hW | hW | hW | hW | hW
  · exact cN levels_mod_const_iff_of_no_down O ϖ hϖ ℓ ell r₁ r₂ a₀ p H b kind U₁ U₂ prL hS hW
  · obtain ⟨s₁, h1, h2, h3⟩ := hW
    exact cD descent_estimate_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₁ h1 h2 h3
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, h5⟩ := hW
    exact cDU descent_estimate_down_up O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 h5
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, ρ, fρ, h5, h6, h7, h8⟩ := hW
    exact cDD levels_mod_const_iff_of_down_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 ρ fρ h5 h6 h7 h8
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, hC, c, α, β, h5, h6⟩ := hW
    exact cUD descent_estimate_up_down O ϖ hϖ ℓ ell r₁ r₂ a₀ rr p H b kind U₁ U₂ prL hS hL hr s₀ s₁ h0 h1 h2 h3
      h4 hC c α β h5 h6

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pow_mem_pair {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ N : ℕ, C (ϖ ^ N) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := by
  unfold CoprimeRat at h
  obtain ⟨N, a, a', hN⟩ := h
  refine ⟨N * (b₁ + b₀), ?_⟩
  have hmem : C (ϖ ^ N) ∈ Ideal.span {p₁} ⊔ Ideal.span {p₀} := by
    rw [← hN]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  have h2 : C (ϖ ^ N) ^ (b₁ + b₀) ∈ (Ideal.span {p₁} ⊔ Ideal.span {p₀}) ^ (b₁ + b₀) :=
    Ideal.pow_mem_pow hmem _
  have h3 := Ideal.sup_pow_add_le_pow_sup_pow h2
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h3
  rw [pow_mul, map_pow, Ideal.span_insert]
  exact h3

theorem consts_DD {ϖ : O} {p₁ p₀ : PowerSeries O} (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) :
    ∃ (ρ : ℕ) (fρ : PowerSeries O),
      C (ϖ ^ ρ) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} ∧
      (∀ k : ℕ, C (ϖ ^ k) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} → ρ ≤ k) ∧
      fρ ∈ Ideal.span {p₁ ^ b₁} ∧ fρ - C (ϖ ^ ρ) ∈ Ideal.span {p₀ ^ b₀} := by
  classical
  have hex := pow_mem_pair h b₁ b₀
  have hρ : C (ϖ ^ Nat.find hex) ∈ Ideal.span {p₁ ^ b₁, p₀ ^ b₀} := Nat.find_spec hex
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hρ
  refine ⟨Nat.find hex, x * p₁ ^ b₁, hρ, fun k hk => Nat.find_min' hex hk,
    Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  rw [← hxy]
  have e : x * p₁ ^ b₁ - (x * p₁ ^ b₁ + y * p₀ ^ b₀) = (-y) * p₀ ^ b₀ := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem consts_UD {ϖ : O} (hϖ : Irreducible ϖ) {d : ℕ} (hd : 1 ≤ d) {p₁ p₀ : PowerSeries O}
    (hp₀ : UnitDist ϖ d p₀) (h : CoprimeRat ϖ p₁ p₀) (b₁ b₀ : ℕ) (hb : 1 ≤ b₀) :
    ∃ (c : ℕ) (α β : PowerSeries O),
      p₁ ^ b₁ = C (ϖ ^ c) * α + p₀ ^ b₀ * β ∧
      p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
  classical
  obtain ⟨N, hN⟩ := pow_mem_pair h b₁ b₀
  have hex : ∃ c : ℕ, p₁ ^ b₁ ∉ Ideal.span {C (ϖ ^ (c + 1)), p₀ ^ b₀} := by
    refine ⟨N, fun hmem => ?_⟩
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hN
    have h1 : C (ϖ ^ N) * (1 - C ϖ * (x * u)) ∈ Ideal.span {p₀ ^ b₀} := by
      rw [Ideal.mem_span_singleton]
      refine ⟨x * v + y, ?_⟩
      have e : C (ϖ ^ (N + 1)) = C (ϖ ^ N) * C ϖ := by rw [pow_succ, map_mul]
      rw [e] at huv
      calc C (ϖ ^ N) * (1 - C ϖ * (x * u))
          = C (ϖ ^ N) - x * (u * (C (ϖ ^ N) * C ϖ)) := by ring
        _ = (x * p₁ ^ b₁ + y * p₀ ^ b₀) - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [hxy]
        _ = (x * (u * (C (ϖ ^ N) * C ϖ) + v * p₀ ^ b₀) + y * p₀ ^ b₀)
              - x * (u * (C (ϖ ^ N) * C ϖ)) := by rw [huv]
        _ = p₀ ^ b₀ * (x * v + y) := by ring
    have h2 := mem_span_pow_of_uniformizer_mul O ϖ hϖ d p₀ hp₀ b₀ N _ h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h2
    have h3 := congrArg (coeff 0) hw
    have h0 := constantCoeff_mem_of_unitDist ϖ d p₀ hp₀ hd
    obtain ⟨e0, he0⟩ := Ideal.mem_span_singleton.1 h0
    obtain ⟨b', rfl⟩ : ∃ b', b₀ = b' + 1 := ⟨b₀ - 1, by omega⟩
    simp only [coeff_zero_eq_constantCoeff, map_sub, map_one, map_mul, map_pow,
      constantCoeff_C] at h3 he0
    have : ϖ ∣ 1 := by
      refine ⟨constantCoeff x * constantCoeff u +
        e0 * (constantCoeff p₀) ^ b' * constantCoeff w, ?_⟩
      have h4 : (1 : O) = ϖ * (constantCoeff x * constantCoeff u) +
          (constantCoeff p₀) ^ (b' + 1) * constantCoeff w := by rw [← h3]; ring
      have h5 : (constantCoeff p₀) ^ (b' + 1) = (constantCoeff p₀) ^ b' * (ϖ * e0) := by
        rw [← he0, pow_succ]
      rw [h5] at h4
      rw [h4]
      ring
    exact hϖ.not_isUnit (isUnit_of_dvd_one this)
  have hs := Nat.find_spec hex
  have hmem : p₁ ^ b₁ ∈ Ideal.span {C (ϖ ^ (Nat.find hex)), p₀ ^ b₀} := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0, pow_zero, map_one]
      have : Ideal.span {(1 : PowerSeries O), p₀ ^ b₀} = ⊤ :=
        Ideal.eq_top_of_unit_mem _ 1 1 (Ideal.subset_span (by simp)) (one_mul 1)
      rw [this]; trivial
    · obtain ⟨c', hc'⟩ : ∃ c', Nat.find hex = c' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (m := c') (by omega)
      rw [hc']
      exact not_not.1 this
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hmem
  exact ⟨Nat.find hex, u, v, huv.symm.trans (by ring), hs⟩

end

end Formalism.ExponentWindows.E.Full

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem word_constants_holds : WordConsts := by
  unfold WordConsts
  intro O _ _ _ ϖ hϖ ℓ ell p b hℓ hP s₀ s₁ h01 h1e
  unfold DistinguishedFamily at hP
  have hs₀ : s₀ < ell := lt_trans h01 h1e
  have hc : CoprimeRat ϖ (p s₁) (p s₀) := hP.2 s₁ h1e s₀ hs₀ (ne_of_gt h01)
  refine ⟨Full.consts_DD hc _ _, fun hb => Full.consts_UD hϖ ?_ (hP.1 s₀ hs₀) hc _ _ hb⟩
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

theorem theorem_E_full_form : ThmEFull := by
  intro O _ _ _ ϖ hϖ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hL₁ hL₂ h1 h2 h3 h4 h5 h6 hr hA
  refine theorem_E_assembled O B n Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM hB
    hL₁ hL₂ h1 h2 h3 h4 h5 h6 ?_
  intro c hc
  obtain ⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', a1, a2, a3, a4, a5, a6, a7, a8, a9,
    a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ :=
    hA c hc
  exact arc_lift_of_localization_data O B n Cu abelian₂ g sig rr a₀ kap V₁ V₂ L₁ L₂ h c r₁ r₂ S₁ S₂ m ϖ H b kind U₁ U₂
    PP PP' a1 hB.1 (hL₂.1 c) a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
    a21 a22 a23 (Full.constLift_of_word hϖ a25 a26 hr a27) a24

end Formalism.ExponentWindows.E
end

section
noncomputable section

namespace Formalism.ExponentWindows.E.LC

open PowerSeries

section Alg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem lift_of_forms (ϖ : O) (hϖ : Irreducible ϖ) {r₁ r₂ : ℕ} (C₁ : Submodule O (Fin r₁ → O))
    (C₂ : Submodule O (Fin r₂ → O)) (hsat : Saturated ϖ C₂)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (hmap : CMap C₁ C₂ prL) (t : O)
    (hcore : ∀ e ∈ C₂, ∀ lam : (Fin r₂ → O) →ₗ[O] O, lam e = 1 → ∀ a : O,
      (∀ v ∈ C₁, lam (prL v) ∈ Ideal.span {a}) → a ∣ t) :
    ∀ v ∈ C₂, ∃ v₁ ∈ C₁, prL v₁ = t • v := by
  classical
  have hle : C₁.map prL ≤ C₂ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hmap v hv
  obtain ⟨o, n, snf⟩ := Submodule.smithNormalFormOfLE (Pi.basisFun O (Fin r₂)) (C₁.map prL) C₂ hle
  obtain ⟨f, hf0, hf1⟩ := exists_proj_of_saturated ϖ hϖ C₂ hsat
  let P : (Fin r₂ → O) →ₗ[O] C₂ := (LinearMap.id - f).codRestrict C₂ (fun v => hf1 v)
  have hP : ∀ (v : Fin r₂ → O) (hv : v ∈ C₂), P v = ⟨v, hv⟩ := by
    intro v hv
    apply Subtype.ext
    simp [P, hf0 v hv]
  have hmem : ∀ (v : Fin r₁ → O) (hv : v ∈ C₁),
      (⟨prL v, hmap v hv⟩ : C₂) ∈ (C₁.map prL).comap C₂.subtype := fun v hv => ⟨v, hv, rfl⟩
  have hbasis : ∀ i : Fin o, t • snf.bM i ∈ (C₁.map prL).comap C₂.subtype := by
    intro i
    have h1 : (snf.bM.coord i ∘ₗ P) (snf.bM i : Fin r₂ → O) = 1 := by
      rw [LinearMap.comp_apply, hP _ (snf.bM i).2]
      simp
    by_cases hi : i ∈ Set.range snf.f
    · obtain ⟨j, rfl⟩ := hi
      obtain ⟨q, hq⟩ := hcore _ (snf.bM (snf.f j)).2 _ h1 (snf.a j) (by
        intro v hv
        rw [LinearMap.comp_apply, hP _ (hmap v hv)]
        have h2 := snf.repr_apply_embedding_eq_repr_smul ⟨_, hmem v hv⟩ (i := j)
        rw [Module.Basis.coord_apply, h2, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩)
      have h3 : t • snf.bM (snf.f j) = q • (snf.bN j : C₂) := by
        rw [snf.snf, smul_smul, hq, mul_comm]
      rw [h3]
      exact Submodule.smul_mem _ _ (snf.bN j).2
    · have h0 := hcore _ (snf.bM i).2 _ h1 0 (by
        intro v hv
        rw [LinearMap.comp_apply, hP _ (hmap v hv)]
        have h2 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem v hv⟩ hi
        rw [Module.Basis.coord_apply, h2]
        exact zero_mem _)
      rw [zero_dvd_iff] at h0
      rw [h0, zero_smul]
      exact zero_mem _
  intro v hv
  have hall : t • (⟨v, hv⟩ : C₂) ∈ (C₁.map prL).comap C₂.subtype := by
    rw [← snf.bM.sum_repr ⟨v, hv⟩, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (hbasis i)
  obtain ⟨v₁, hv₁, h⟩ := hall
  exact ⟨v₁, hv₁, by simpa using h⟩

theorem lam_dvd (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) (Y : PowerSeries O) (h : ∀ s < ell, p s ^ K s ∣ Y) :
    abelian₂ p K ell ∣ Y := by
  unfold abelian₂
  apply prod_dvd_of_coprimeRat ϖ (Finset.range ell) (fun s => p s ^ K s)
  · intro s hs
    exact isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)) _
  · intro s hs t ht hne
    exact coprimeRat₂_pow_pow ϖ _ _ (hp.2 s (Finset.mem_range.1 hs) t (Finset.mem_range.1 ht) hne) _ _
  · intro s hs
    exact h s (Finset.mem_range.1 hs)

theorem lam_isSat (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) : IsSat ϖ (abelian₂ p K ell) := by
  unfold abelian₂
  apply isSat_prod ϖ (Finset.range ell) (fun s => p s ^ K s)
  intro s hs
  exact isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)) _

theorem lam_ne_zero (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (K : ℕ → ℕ) : abelian₂ p K ell ≠ 0 := by
  unfold abelian₂
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  exact pow_ne_zero _ (ne_zero_of_unitDist ϖ hϖ _ _ (hp.1 s (Finset.mem_range.1 hs)))

theorem lamLess_eq (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s₁ b : ℕ) (hs : s₁ < ell) :
    LamLess p H ell s₁ b = abelian₂ p (Function.update H s₁ (H s₁ - b)) ell := by
  rw [lam_eq_pow_mul p _ ell s₁ hs, LamLess, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

theorem lam_eq_lamLess (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s₁ b : ℕ) (hs : s₁ < ell)
    (hb : b ≤ H s₁) : abelian₂ p H ell = LamLess p H ell s₁ b * p s₁ ^ b := by
  rw [lam_eq_pow_mul p H ell s₁ hs, LamLess]
  have h1 : p s₁ ^ H s₁ = p s₁ ^ (H s₁ - b) * p s₁ ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hb]
  rw [h1]
  ring

variable {r : ℕ}

theorem levelCond_dvd_sub (ϖ : O) (hϖ : Irreducible ϖ) {d : ℕ} {p : PowerSeries O}
    (hp : UnitDist ϖ d p) (H b : ℕ) (k : Kind) (V : Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (h : LevelCond ϖ p H b k V y) (g : (Fin r → O) →ₗ[O] O) :
    p ^ (H - b) ∣ linExt g y := by
  have hd : p ^ (H - b) ∣ p ^ H := pow_dvd_pow p (Nat.sub_le H b)
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_of_dvd_left hd _
  | up =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hd _)
  | down =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_of_dvd_left hd _)
      (dvd_mul_of_dvd_left (hd.trans (pow_dvd_pow p (Nat.le_add_right H b))) _)

theorem levelCond_dvd (ϖ : O) (hϖ : Irreducible ϖ) {d : ℕ} {p : PowerSeries O}
    (hp : UnitDist ϖ d p) (H b : ℕ) (k : Kind) (V : Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (h : LevelCond ϖ p H b k V y) (g : (Fin r → O) →ₗ[O] O)
    (hg : k = Kind.up → ∀ v ∈ V, g v = 0) : p ^ H ∣ linExt g y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_right _ _
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      linExt_eq_zero_of_mem_ext g V (hg rfl) c hc, mul_zero, zero_add] at h1
    rw [h1]
    exact dvd_mul_right _ _
  | down =>
    obtain ⟨N, c, z, _, hz⟩ := h
    apply isSat_pow_of_unitDist ϖ hϖ d p hp _ N
    have h1 := congrArg (linExt g) hz
    rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (pow_dvd_pow p (Nat.le_add_right H b)) _)

theorem NN_dvd_lamLess (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ) (hs₁ : s₁ < ell)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (g : (Fin r → O) →ₗ[O] O) :
    LamLess p H ell s₁ (b s₁) ∣ linExt g y := by
  rw [lamLess_eq p H ell s₁ (b s₁) hs₁]
  apply lam_dvd ϖ hϖ hp
  intro s hs
  by_cases h1 : s = s₁
  · subst h1
    rw [Function.update_self]
    exact levelCond_dvd_sub ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g
  · rw [Function.update_of_ne h1]
    exact levelCond_dvd ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g
      (fun hk => absurd hk (honly s hs h1))

theorem NN_dvd_lam (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (g : (Fin r → O) →ₗ[O] O)
    (hg : ∀ v ∈ V s₁, g v = 0) : abelian₂ p H ell ∣ linExt g y := by
  apply lam_dvd ϖ hϖ hp
  intro s hs
  refine levelCond_dvd ϖ hϖ (hp.1 s hs) _ _ _ _ y (hy s hs) g (fun hk => ?_)
  by_cases h1 : s = s₁
  · subst h1
    exact hg
  · exact absurd hk (honly s hs h1)

theorem NN_form (ϖ : O) (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hp : DistinguishedFamily ϖ ℓ ell p) (H b : ℕ → ℕ) (kind : ℕ → Kind) (V : ℕ → Submodule O (Fin r → O))
    (y : Fin r → PowerSeries O) (hy : NN ϖ p H b kind V ell y) (s₁ : ℕ) (hs₁ : s₁ < ell)
    (honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up) (hsat : Saturated ϖ (V s₁))
    (μ : (Fin r → O) →ₗ[O] O) (a : O) (ha : ∀ v ∈ V s₁, μ v ∈ Ideal.span {a}) :
    ∃ Y' Y'' : PowerSeries O,
      linExt μ y = LamLess p H ell s₁ (b s₁) * (C a * Y') + abelian₂ p H ell * Y'' := by
  obtain ⟨f, hf0, hf1⟩ := exists_proj_of_saturated ϖ hϖ (V s₁) hsat
  obtain ⟨Y'', hY''⟩ := NN_dvd_lam ϖ hϖ hp H b kind V y hy s₁ honly (μ ∘ₗ f)
    (fun v hv => by rw [LinearMap.comp_apply, hf0 v hv, map_zero])
  have hG := NN_dvd_lamLess ϖ hϖ hp H b kind V y hy s₁ hs₁ honly (μ - μ ∘ₗ f)
  have hCa : C a ∣ linExt (μ - μ ∘ₗ f) y := by
    rw [linExt_apply]
    refine Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right ?_ _
    have h1 : (μ - μ ∘ₗ f) (Pi.single i 1) = μ (Pi.single i 1 - f (Pi.single i 1)) := by
      rw [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
    rw [h1]
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (ha _ (hf1 (Pi.single i 1)))
    rw [hq, map_mul]
    exact dvd_mul_right _ _
  obtain ⟨Y₀, hY₀⟩ := hCa
  have hsplit : linExt μ y = linExt (μ - μ ∘ₗ f) y + linExt (μ ∘ₗ f) y := by
    rw [linExt_sub]
    ring
  by_cases ha0 : a = 0
  · refine ⟨0, Y'', ?_⟩
    rw [hsplit, hY₀, hY'', ha0]
    simp
  · obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : LamLess p H ell s₁ (b s₁) ∣ Y₀ := by
      have hS : IsSat ϖ (LamLess p H ell s₁ (b s₁)) := by
        rw [lamLess_eq p H ell s₁ (b s₁) hs₁]
        exact lam_isSat ϖ hϖ hp _
      have h2 : LamLess p H ell s₁ (b s₁) ∣ C (ϖ ^ k) * (C (u : O) * Y₀) := by
        have h3 : C (ϖ ^ k) * (C (u : O) * Y₀) = C a * Y₀ := by
          rw [hu, map_mul]
          ring
        rw [h3, ← hY₀]
        exact hG
      have h4 := hS k _ h2
      have hunit : IsUnit (C (u : O) : PowerSeries O) := u.isUnit.map C
      exact (hunit.dvd_mul_left).1 h4
    obtain ⟨Y', hY'⟩ := hdvd
    refine ⟨Y', Y'', ?_⟩
    rw [hsplit, hY₀, hY'', hY']
    ring

theorem linExt_extL {r₁ r₂ : ℕ} (lam : (Fin r₂ → O) →ₗ[O] O)
    (prL : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) (y : Fin r₁ → PowerSeries O) :
    linExt lam (extL prL y) = linExt (lam ∘ₗ prL) y := by
  classical
  have hy : y = ∑ i, y i • cst (Pi.single i (1 : O)) := by
    funext j
    simp [cst, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  rw [map_sum, map_sum, linExt_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, CL.extL_cst, linExt_cst]
  rfl

theorem lattice_condition_up_down_pair (ϖ : O) (p : ℕ → PowerSeries O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (V : ℕ → Submodule O (Fin r → O)) (ell s₀ s₁ : ℕ) (hk1 : kind s₁ = Kind.up)
    (hk0 : kind s₀ = Kind.down) (hthin : ∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin)
    (e : Fin r → O) (he : e ∈ V s₁) :
    NN ϖ p H b kind V ell ((p s₀ ^ b s₀ * LamLess p H ell s₁ (b s₁)) • cst e) := by
  intro s hs
  by_cases h1 : s = s₁
  · subst h1
    rw [hk1]
    refine ⟨0, (p s₀ ^ b s₀ * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t) • cst e, 0,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, he, rfl⟩), ?_⟩
    simp only [pow_zero, map_one, smul_zero, add_zero, smul_smul, LamLess]
    congr 1
    ring
  · have hd : p s ^ H s ∣ LamLess p H ell s₁ (b s₁) :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun t => p t ^ H t)
        (Finset.mem_erase.2 ⟨h1, Finset.mem_range.2 hs⟩)) _
    obtain ⟨q, hq⟩ := hd
    by_cases h0 : s = s₀
    · subst h0
      rw [hk0]
      refine ⟨0, 0, q • cst e, zero_mem _, ?_⟩
      rw [hq]
      simp only [pow_zero, map_one, smul_zero, zero_add, smul_smul]
      congr 1
      rw [pow_add]
      ring
    · rw [hthin s hs h0 h1]
      refine ⟨0, (p s₀ ^ b s₀ * q) • cst e, ?_⟩
      rw [hq]
      simp only [pow_zero, map_one, smul_smul]
      congr 1
      ring

end Alg

section Levels

variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} {h : LatHom L₁ L₂} {c : ZMod n} {ell : ℕ}
  {Λ : PowerSeries O} {r₁ r₂ : ℕ} {S₁ : LevelData L₁ c ell Λ r₁} {S₂ : LevelData L₂ c ell Λ r₂}

theorem levels (m : LevelMap h S₁ S₂) (ϖ : O) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O)) (g sig rr : ℕ)
    (hRD₁ : S₁.RD g) (hRD₂ : S₂.RD g) (hPa₁ : S₁.Partner sig) (hPa₂ : S₂.Partner sig)
    (hP3₁ : S₁.P3) (hP3₂ : S₂.P3) (hP4a₁ : S₁.DivisibleIff g) (hP4a₂ : S₂.DivisibleIff g)
    (hBr₁ : S₁.Bridge ϖ H b kind U₁) (hBr₂ : S₂.Bridge ϖ H b kind U₂) (hFl : S₂.FlReg ϖ H)
    (hMap : m.MapFl) (hP4d : h.LiftsDivisible c ell g rr)
    (y₂ : Fin r₂ → PowerSeries O) (hy₂ : NN ϖ B.p H b kind U₂ ell y₂) :
    ∃ y₁ : Fin r₁ → PowerSeries O, NN ϖ B.p H b kind U₁ ell (B.Th ell g ^ 2 • y₁) ∧
      ∀ s < ell, ∃ (N : ℕ) (z : Fin r₂ → PowerSeries O),
        C (ϖ ^ N) • (extL m.prL y₁ - C ((B.ℓ : O) ^ (2 * sig + rr)) • y₂) = B.p s ^ H s • z := by
  have hb₂ := (hBr₂.1 y₂).2 hy₂

  obtain ⟨w, hw⟩ := hPa₂.2 y₂
  have hw1 : ∀ s < ell, S₂.loc s w ∈ dv (B.p s ^ g) (S₂.Nl s) := by
    intro s hs
    have h1 : B.lc ^ sig • S₂.locL s y₂ ∈ dv (B.p s ^ g) (S₂.Nl s) :=
      Submodule.smul_mem _ _ ((hRD₂ s hs).1 (hb₂ s hs))
    have h2 : S₂.loc s w - B.lc ^ sig • S₂.locL s y₂ ∈ dv (B.p s ^ g) (S₂.Nl s) :=
      IteratedPhiHomomorphisms.le_dv _ _ ((hP3₂ s hs).1 (hw s hs))
    have h3 := Submodule.add_mem _ h2 h1
    rwa [sub_add_cancel] at h3
  have hwΘ : (w : V₂) ∈ dv (B.Th ell g) (L₂.N c) := (hP4a₂.2 w).2 hw1

  obtain ⟨x₁, hx₁, hfx⟩ := hP4d _ hwΘ
  have hx₁W : x₁ ∈ L₁.W c ell Λ := hP4a₁.1 hx₁
  have hx₁l := (hP4a₁.2 ⟨x₁, hx₁W⟩).1 hx₁

  obtain ⟨y₁, hy₁⟩ := hPa₁.1 ⟨x₁, hx₁W⟩
  refine ⟨y₁, ?_, ?_⟩
  · apply (hBr₁.1 _).1
    intro s hs
    have h1 : S₁.locL s y₁ ∈ dv (B.p s ^ g) (S₁.Nl s) := by
      have a1 := IteratedPhiHomomorphisms.le_dv (B.p s ^ g) _ ((hP3₁ s hs).1 (hy₁ s hs))
      have a2 := Submodule.smul_mem _ (B.lc ^ sig) (hx₁l s hs)
      have a3 := Submodule.add_mem _ a1 a2
      rwa [sub_add_cancel] at a3
    have h2 : B.p s ^ g • (B.p s ^ g • S₁.locL s y₁) ∈ S₁.Nb s :=
      IteratedPhiHomomorphisms.mem_dv.1 ((hRD₁ s hs).2 (IteratedPhiHomomorphisms.mem_dv.1 h1))
    have hΘ : B.Th ell g = B.p s ^ g * ∏ t ∈ (Finset.range ell).erase s, B.p t ^ g :=
      (Finset.mul_prod_erase _ (fun t => B.p t ^ g) (Finset.mem_range.2 hs)).symm
    have h3 : (B.p s ^ g * ∏ t ∈ (Finset.range ell).erase s, B.p t ^ g) ^ 2 • S₁.locL s y₁ =
        (∏ t ∈ (Finset.range ell).erase s, B.p t ^ g) ^ 2 •
          (B.p s ^ g • (B.p s ^ g • S₁.locL s y₁)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [map_smul, hΘ, h3]
    exact Submodule.smul_mem _ _ h2

  · intro s hs
    apply hFl s hs
    have hfW : h.f x₁ ∈ L₂.W c ell Λ := by
      rw [hfx]
      exact Submodule.smul_mem _ _ w.2
    have e1 := m.loc_comm s hs x₁ hx₁W hfW
    have e2 : S₂.loc s ⟨h.f x₁, hfW⟩ = B.lc ^ rr • S₂.loc s w := by
      rw [← map_smul]
      congr 1
      exact Subtype.ext hfx
    have a1 := hMap s hs _ (hy₁ s hs)
    rw [map_sub, map_smul, e1, e2, m.locL_comm s hs] at a1
    have a2 := Submodule.smul_mem _ (B.lc ^ (sig + rr)) (hw s hs)
    have a3 := Submodule.add_mem _ a1 a2
    rw [map_sub, map_smul]
    convert a3 using 1
    have hexp : 2 * sig + rr = sig + rr + sig := by ring
    rw [← IteratedPhiHomomorphisms.lc_pow, smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add, hexp]
    abel

end Levels

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} {h : LatHom L₁ L₂} {c : ZMod n}
  {ell : ℕ} {Λ : PowerSeries O} {r₁ r₂ : ℕ} {S₁ : LevelData L₁ c ell Λ r₁}
  {S₂ : LevelData L₂ c ell Λ r₂}

theorem core (ϖ : O) (hϖ : Irreducible ϖ) (m : LevelMap h S₁ S₂) (H b : ℕ → ℕ) (kind : ℕ → Kind)
    (U₁ : ℕ → Submodule O (Fin r₁ → O)) (U₂ : ℕ → Submodule O (Fin r₂ → O)) (g sig rr : ℕ)
    (hset : LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂)
    (hRD₁ : S₁.RD g) (hRD₂ : S₂.RD g) (hPa₁ : S₁.Partner sig) (hPa₂ : S₂.Partner sig)
    (hP3₁ : S₁.P3) (hP3₂ : S₂.P3) (hP4a₁ : S₁.DivisibleIff g) (hP4a₂ : S₂.DivisibleIff g)
    (hBr₁ : S₁.Bridge ϖ H b kind U₁) (hBr₂ : S₂.Bridge ϖ H b kind U₂) (hFl : S₂.FlReg ϖ H)
    (hMap : m.MapFl) (hP4d : h.LiftsDivisible c ell g rr)
    (s₀ s₁ : ℕ) (hs₁ : s₁ < ell) (hk1 : kind s₁ = Kind.up)
    (hk0 : kind s₀ = Kind.down) (hthin : ∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin)
    (e : Fin r₂ → O) (he : e ∈ U₂ s₁) (lam : (Fin r₂ → O) →ₗ[O] O) (a : O)
    (ha : ∀ v ∈ U₁ s₁, lam (m.prL v) ∈ Ideal.span {a}) :
    C (lam e) * (C ((B.ℓ : O) ^ (2 * sig + rr)) * B.Th ell g ^ 2 * B.p s₀ ^ b s₀) ∈
      Ideal.span {C a, B.p s₁ ^ b s₁} := by
  obtain ⟨_, hp, hsat₁, _, hbH⟩ := hset
  have honly : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.up := by
    intro s hs h1 hk
    by_cases h0 : s = s₀
    · rw [h0, hk0] at hk
      exact Kind.noConfusion hk
    · rw [hthin s hs h0 h1] at hk
      exact Kind.noConfusion hk
  obtain ⟨y₁, hNN₁, hδ⟩ := levels m ϖ H b kind U₁ U₂ g sig rr hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁
    hP4a₂ hBr₁ hBr₂ hFl hMap hP4d _ (lattice_condition_up_down_pair ϖ B.p H b kind U₂ ell s₀ s₁ hk1 hk0 hthin e he)
  have hd : abelian₂ B.p H ell ∣ linExt lam (extL m.prL y₁ - C ((B.ℓ : O) ^ (2 * sig + rr)) •
      ((B.p s₀ ^ b s₀ * LamLess B.p H ell s₁ (b s₁)) • cst e)) := by
    apply lam_dvd ϖ hϖ hp
    intro s hs
    obtain ⟨N, z, hz⟩ := hδ s hs
    apply isSat_pow_of_unitDist ϖ hϖ _ _ (hp.1 s hs) _ N
    have h1 := congrArg (linExt lam) hz
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    rw [h1]
    exact dvd_mul_right _ _
  obtain ⟨d', hd'⟩ := hd
  obtain ⟨Y', Y'', hY⟩ := NN_form ϖ hϖ hp H b kind U₁ _ hNN₁ s₁ hs₁ honly (hsat₁ s₁ hs₁)
    (lam ∘ₗ m.prL) a ha
  rw [map_smul, ← linExt_extL, smul_eq_mul] at hY
  rw [map_sub, map_smul, map_smul, linExt_cst, smul_eq_mul, smul_eq_mul] at hd'
  have hΛ := lam_eq_lamLess B.p H ell s₁ (b s₁) hs₁ (hbH s₁ hs₁ hk1)
  have hG : LamLess B.p H ell s₁ (b s₁) ≠ 0 := by
    rw [lamLess_eq B.p H ell s₁ (b s₁) hs₁]
    exact lam_ne_zero ϖ hϖ hp _
  rw [hΛ] at hY hd'
  have key : LamLess B.p H ell s₁ (b s₁) *
      (C (lam e) * (C ((B.ℓ : O) ^ (2 * sig + rr)) * B.Th ell g ^ 2 * B.p s₀ ^ b s₀)) =
      LamLess B.p H ell s₁ (b s₁) *
        (Y' * C a + (Y'' - B.Th ell g ^ 2 * d') * B.p s₁ ^ b s₁) := by
    linear_combination hY - B.Th ell g ^ 2 * hd'
  rw [Ideal.mem_span_pair]
  exact ⟨Y', Y'' - B.Th ell g ^ 2 * d', (mul_left_cancel₀ hG key).symm⟩

end Core

theorem shape_ext {O : Type} [CommRing O] [Nontrivial O] (B : Base O) (ell : ℕ) (hℓ : 2 ≤ B.ℓ)
    (hsh : B.PShape ell) :
    ∃ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O), (∀ s, (E s).Monic) ∧
      (∀ s, (E s).natDegree = B.ℓ ^ s) ∧ (∀ s, ∀ i < B.ℓ ^ s, (B.ℓ : O) ∣ (E s).coeff i) ∧
      (∀ s, Associated ((E s).coeff 0) (B.ℓ : O)) ∧ (∀ s, IsUnit (u s)) ∧
      ∀ s < ell, B.p s = u s * (E s : PowerSeries O) := by
  have hall : ∀ s, ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = B.ℓ ^ s ∧
      (∀ i < B.ℓ ^ s, (B.ℓ : O) ∣ E.coeff i) ∧ Associated (E.coeff 0) (B.ℓ : O) ∧ IsUnit u ∧
      (s < ell → B.p s = u * (E : PowerSeries O)) := by
    intro s
    by_cases hs : s < ell
    · obtain ⟨E, u, h1, h2, h3, h4, h5, h6⟩ := hsh s hs
      exact ⟨E, u, h1, h2, h3, h4, h5, fun _ => h6⟩
    · have hpos : B.ℓ ^ s ≠ 0 := pow_ne_zero _ (by omega)
      refine ⟨Polynomial.X ^ (B.ℓ ^ s) + Polynomial.C (B.ℓ : O), 1,
        Polynomial.monic_X_pow_add_C _ hpos, Polynomial.natDegree_X_pow_add_C, ?_, ?_, isUnit_one,
        fun h => absurd h hs⟩
      · intro i hi
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega), zero_add,
          Polynomial.coeff_C]
        split_ifs
        · exact dvd_rfl
        · exact dvd_zero _
      · rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (fun h => hpos h.symm), zero_add,
          Polynomial.coeff_C_zero]
  choose E u h1 h2 h3 h4 h5 h6 using hall
  exact ⟨E, u, h1, h2, h3, h4, h5, h6⟩

end Formalism.ExponentWindows.E.LC

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem lemma_C_full_holds : LemmaCFull := by
  intro hVal O _ _ _ ϖ hϖ B e he hℓe n V₁ V₂ _ _ _ _ L₁ L₂ h c ell Λ r₁ r₂ S₁ S₂ m H b kind U₁ U₂
    g sig rr a₀ _ hsh hset hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁ hP4a₂ hBr₁ hBr₂ hFl hMap hP4d
    s₀ s₁ h01 hs₁ hk1 hk0 hthin hC hA hB1 hB0
  have hs₀ : s₀ < ell := h01.trans hs₁
  obtain ⟨E, u, hE1, hE2, hE3, hE4, hu, hpE⟩ := LC.shape_ext B ell hset.1 hsh
  refine LC.lift_of_forms ϖ hϖ (U₁ s₁) (U₂ s₁) (hset.2.2.2.1 s₁ hs₁) m.prL hC _ ?_
  intro v hv lam hlam a ha
  have hc := LC.core ϖ hϖ m H b kind U₁ U₂ g sig rr hset hRD₁ hRD₂ hPa₁ hPa₂ hP3₁ hP3₂ hP4a₁ hP4a₂
    hBr₁ hBr₂ hFl hMap hP4d s₀ s₁ hs₁ hk1 hk0 hthin v hv lam a ha
  rw [hlam, map_one, one_mul] at hc
  have hTh : B.Th ell g = ∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g := by
    unfold Base.Th
    apply Finset.prod_congr rfl
    intro s hs
    rw [hpE s (Finset.mem_range.1 hs)]
  rw [hTh, hpE s₀ hs₀, hpE s₁ hs₁] at hc
  have hA' : (((2 * sig + rr : ℕ) : ℝ) + 2 * g * ell) ≤ a₀ := by exact_mod_cast hA
  have hB1' : 2 * (a₀ : ℝ) < b s₁ := by exact_mod_cast hB1
  have hbound : ∀ k : ℕ, C ((B.ℓ : O) ^ (2 * sig + rr)) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b s₀ ∈
      Ideal.span {C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b s₁} → k ≤ e * (2 * a₀) := by
    intro k hk
    have h2 := (hVal O ϖ hϖ B.ℓ e hset.1 he hℓe E u hE1 hE2 hE3 hE4 hu ell g (2 * sig + rr) (b s₀)
      (b s₁) s₀ s₁ k h01 (by linarith) hB0 hk).2
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have h3 : (k : ℝ) ≤ ((e * (2 * a₀) : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h3
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hc
  by_cases ha0 : a = 0
  · exfalso
    have h1 := hbound (e * (2 * a₀) + 1) (Ideal.mem_span_pair.2 ⟨0, y, by
      rw [← hxy, ha0]
      simp⟩)
    omega
  · obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have h1 := hbound k (Ideal.mem_span_pair.2 ⟨x * C (w : O), y, by
      rw [← hxy, hw, map_mul]
      ring⟩)
    have h2 : ϖ ^ k ∣ (ϖ ^ e) ^ (2 * a₀) := by
      rw [← pow_mul]
      exact pow_dvd_pow _ h1
    rw [hw]
    exact Units.mul_left_dvd.2 (h2.trans (hℓe.pow_pow (n := 2 * a₀)).symm.dvd)

end Formalism.ExponentWindows.E
end
end

section
namespace Formalism.ExponentWindows.E.Prim

open PowerSeries

theorem lt_parM (ℓ hh g : ℕ) (hℓ : 2 ≤ ℓ) : hh + 2 * g < (ℓ - 1) * parM ℓ hh g := by
  unfold parM
  have hm : 0 < ℓ - 1 := by omega
  first
    | exact Nat.lt_mul_div_succ _ hm
    | (have h1 := Nat.div_add_mod (hh + 2 * g) (ℓ - 1)
       have h2 := Nat.mod_lt (hh + 2 * g) hm
       nlinarith)

section shape
variable {O : Type} [CommRing O]

def QQ (l : O) (x : PowerSeries O) (d : ℕ) : Prop :=
  ∃ v a : PowerSeries O, IsUnit v ∧ x = v * X ^ d + C l * a

theorem QQ.mul {l : O} {x y : PowerSeries O} {d d' : ℕ} (hx : QQ l x d) (hy : QQ l y d') :
    QQ l (x * y) (d + d') := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨w, b, hw, rfl⟩ := hy
  refine ⟨v * w, v * X ^ d * b + a * (w * X ^ d') + C l * a * b, hv.mul hw, ?_⟩
  ring

theorem QQ.pow {l : O} {x : PowerSeries O} {d : ℕ} (hx : QQ l x d) (m : ℕ) :
    QQ l (x ^ m) (d * m) := by
  induction m with
  | zero => exact ⟨1, 0, isUnit_one, by simp⟩
  | succ m ih =>
    rw [pow_succ]
    have h := ih.mul hx
    rwa [show d * m + d = d * (m + 1) by ring] at h

theorem QQ.unit_mul {l : O} {x u : PowerSeries O} {d : ℕ} (hu : IsUnit u) (hx : QQ l x d) :
    QQ l (u * x) d := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  exact ⟨u * v, u * a, hu.mul hv, by ring⟩

theorem QQ.map {l : O} (f : PowerSeries O →ₐ[O] PowerSeries O) {x : PowerSeries O} {e d : ℕ}
    (hf : QQ l (f X) e) (hx : QQ l x d) : QQ l (f x) (e * d) := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨w, b, hw, hwb⟩ := QQ.unit_mul (hv.map f) (hf.pow d)
  have hC : f (C l) = C l := by
    first
      | exact f.commutes l
      | simpa [PowerSeries.algebraMap_eq] using f.commutes l
  refine ⟨w, b + f a, hw, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, hC, hwb]
  ring

theorem QQ_φX {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) : QQ (B.ℓ : O) (B.φ X) B.ℓ := by
  obtain ⟨u, hu⟩ := h3
  have hq : QQ (B.ℓ : O) B.q 1 := ⟨1, 1, isUnit_one, by simp [Base.q]⟩
  have hX : QQ (B.ℓ : O) (X : PowerSeries O) 1 := ⟨1, 0, isUnit_one, by simp⟩
  have h := QQ.unit_mul u.isUnit (hX.mul (hq.pow (B.ℓ - 1)))
  have he : 1 + 1 * (B.ℓ - 1) = B.ℓ := by omega
  rw [he] at h
  rw [hu, mul_assoc]
  exact h

theorem QQ_it {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (s : ℕ) :
    QQ (B.ℓ : O) ((⇑B.φ)^[s] X) (B.ℓ ^ s) := by
  induction s with
  | zero => exact ⟨1, 0, isUnit_one, by simp⟩
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have h := QQ.map B.φ (QQ_φX h3 h1) ih
    rwa [show B.ℓ * B.ℓ ^ s = B.ℓ ^ (s + 1) by ring] at h

theorem p_eq (B : Base O) (s : ℕ) : B.p s = (⇑B.φ)^[s] X + C (B.ℓ : O) := by
  have hC : ∀ c : O, B.φ (C c) = C c := fun c => by
    first
      | exact B.φ.commutes c
      | simpa [PowerSeries.algebraMap_eq] using B.φ.commutes c
  unfold Base.p Base.q
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add, hC]

theorem QQ_p {B : Base O} (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (s : ℕ) :
    QQ (B.ℓ : O) (B.p s) (B.ℓ ^ s) := by
  obtain ⟨v, a, hv, ha⟩ := QQ_it h3 h1 s
  exact ⟨v, a + 1, hv, by rw [p_eq, ha]; ring⟩

theorem isUnit_one_add [IsLocalRing O] {l : O} (hl : ¬ IsUnit l) (c : O) : IsUnit (1 + l * c) := by
  by_contra h
  have h1 : ¬ IsUnit (l * c) := fun hu => hl (isUnit_of_mul_isUnit_left hu)
  have h2 : ¬ IsUnit (-(l * c)) := by rwa [IsUnit.neg_iff]
  exact IsLocalRing.nonunits_add h h2 (by simp)

theorem prep [IsLocalRing O] {l : O} (hl : ¬ IsUnit l) [IsAdicComplete (Ideal.span {l}) O]
    {x : PowerSeries O} {d : ℕ} (hx : QQ l x d) :
    ∃ (E : Polynomial O) (u : PowerSeries O), E.Monic ∧ E.natDegree = d ∧
      (∀ i < d, l ∣ E.coeff i) ∧ IsUnit u ∧ x = u * (E : PowerSeries O) := by
  obtain ⟨v, a, hv, rfl⟩ := hx
  obtain ⟨vi, hvi⟩ := hv.exists_right_inv
  have hI : Ideal.span {l} ≠ ⊤ := Ideal.span_singleton_ne_top hl
  have : Nontrivial (O ⧸ Ideal.span {l}) := Ideal.Quotient.nontrivial_iff.2 hI
  set g : PowerSeries O := X ^ d + C l * (vi * a) with hg
  have hl0 : Ideal.Quotient.mk (Ideal.span {l}) l = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self l)
  have hmap : g.map (Ideal.Quotient.mk (Ideal.span {l})) = X ^ d := by
    rw [hg, map_add, map_mul, map_pow, map_X, map_C, hl0, map_zero, zero_mul, add_zero]
  have hord : (g.map (Ideal.Quotient.mk (Ideal.span {l}))).order.toNat = d := by
    rw [hmap, order_X_pow]
    rfl
  have H : g.IsWeierstrassDivisorAt (Ideal.span {l}) := by
    unfold IsWeierstrassDivisorAt
    rw [hord, hg, map_add, coeff_X_pow_self, coeff_C_mul]
    exact isUnit_one_add hl _
  have hdv := H.isWeierstrassDivisionAt_div_mod (X ^ d)
  set q := H.div (X ^ d)
  set r := H.mod (X ^ d)
  have h1 : r.degree < d := by
    have := hdv.degree_lt
    rwa [hord] at this
  have h2 : (X : PowerSeries O) ^ d = g * q + r := hdv.eq_mul_add
  have hm : (Polynomial.X ^ d - r).Monic := Polynomial.monic_X_pow_sub h1
  have hnd : (Polynomial.X ^ d - r).natDegree = d := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  have hE : ((Polynomial.X ^ d - r : Polynomial O) : PowerSeries O) = g * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, h2]
    ring
  have hq : IsUnit q := by
    rw [isUnit_iff_constantCoeff]
    have hcd : (Polynomial.X ^ d - r : Polynomial O).coeff d = 1 := by
      have := hm.coeff_natDegree
      rwa [hnd] at this
    have h3 := congrArg (coeff d) hE
    rw [Polynomial.coeff_coe, hcd, hg, add_mul, map_add,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, mul_assoc, coeff_C_mul,
      coeff_zero_eq_constantCoeff_apply] at h3
    have h4 : constantCoeff q = 1 + l * (-(coeff d (vi * a * q))) := by
      rw [h3]; ring
    rw [h4]
    exact isUnit_one_add hl _
  obtain ⟨qi, hqi⟩ := hq.exists_right_inv
  refine ⟨Polynomial.X ^ d - r, v * qi, hm, hnd, fun i hi => ?_,
    hv.mul (IsUnit.of_mul_eq_one q (by rw [mul_comm]; exact hqi)), ?_⟩
  · have := hdv.coeff_f_sub_r_mem (i := i) (by rwa [hord])
    rw [Ideal.mem_span_singleton] at this
    have e : coeff i ((X : PowerSeries O) ^ d - (r : PowerSeries O)) =
        (Polynomial.X ^ d - r : Polynomial O).coeff i := by
      rw [← Polynomial.coeff_coe, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X]
    rwa [e] at this
  · rw [hE, hg]
    linear_combination (-(C l * a)) * hvi - (v * (X ^ d + C l * (vi * a))) * hqi

end shape

section dvr
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem pshape {B : Base O} (hl : ¬ IsUnit (B.ℓ : O)) [IsAdicComplete (Ideal.span {(B.ℓ : O)}) O]
    (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (ell : ℕ) : B.PShape ell := by
  intro s _
  obtain ⟨E, u, hm, hd, hc, hu, hp⟩ := prep hl (QQ_p h3 h1 s)
  refine ⟨E, u, hm, hd, hc, ?_, hu, hp⟩
  obtain ⟨w, hw⟩ := iterated_third_estimate_holds O B h3 s
  have h0 : constantCoeff (B.p s) = (B.ℓ : O) := by
    rw [p_eq, hw]
    simp
  rw [hp, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O),
    Polynomial.coeff_coe] at h0
  have hu0 : IsUnit (constantCoeff u) := isUnit_iff_constantCoeff.1 hu
  exact ⟨hu0.unit, by rw [IsUnit.unit_spec, mul_comm]; exact h0⟩

noncomputable def itAlg (f : PowerSeries O →ₐ[O] PowerSeries O) :
    ℕ → (PowerSeries O →ₐ[O] PowerSeries O)
  | 0 => AlgHom.id O _
  | k + 1 => f.comp (itAlg f k)

theorem itAlg_apply (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (a : PowerSeries O) :
    itAlg f k a = (⇑f)^[k] a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem basePhiFree {B : Base O} (hl : ¬ IsUnit (B.ℓ : O))
    [IsAdicComplete (Ideal.span {(B.ℓ : O)}) O] (h3 : B.E3) (h1 : 1 ≤ B.ℓ) (k : ℕ) :
    (∀ a : PowerSeries O, ∃ a' : Fin (B.ℓ ^ k) → PowerSeries O,
      a = ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) ∧
    ∀ a' : Fin (B.ℓ ^ k) → PowerSeries O,
      ∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t) = 0 →
      ∀ t, a' t = 0 := by
  obtain ⟨E, u, hm, hdeg, hc, hu, hPe'⟩ := prep hl (QQ_it h3 h1 k)
  set d := B.ℓ ^ k with hd
  have hd1 : 1 ≤ d := Nat.one_le_pow _ _ h1
  set φ := itAlg B.φ k with hφ
  have hPe : φ X = u * (E : PowerSeries O) := by rw [hφ, itAlg_apply]; exact hPe'
  have hI : Ideal.span {(B.ℓ : O)} ≠ ⊤ := Ideal.span_singleton_ne_top hl
  have hE : E.IsDistinguishedAt (Ideal.span {(B.ℓ : O)}) :=
    ⟨⟨fun {i} hi => Ideal.mem_span_singleton.2 (hc i (hdeg ▸ hi))⟩, hm⟩
  have hPnu : ¬ IsUnit (φ X) := by
    intro hunit
    have h1 := isUnit_constantCoeff _ hunit
    have hmem0 : constantCoeff (φ X) ∈ Ideal.span {(B.ℓ : O)} := by
      rw [hPe, map_mul, ← coeff_zero_eq_constantCoeff_apply (E : PowerSeries O),
        Polynomial.coeff_coe]
      exact Ideal.mul_mem_left _ _ (hE.mem (by omega))
    exact hI (Ideal.eq_top_of_isUnit_mem _ hmem0 h1)
  have hP0 : φ X ≠ 0 := by
    intro h0
    rw [hPe] at h0
    have hE0 : (E : PowerSeries O) = 0 := (hu.mul_right_eq_zero).mp h0
    rw [Polynomial.coe_eq_zero_iff] at hE0
    exact hE.monic.ne_zero hE0
  have hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r := by
    intro F
    obtain ⟨q, r, hr, hF⟩ := exists_div_of_isDistinguishedAt hI hE F
    refine ⟨↑hu.unit⁻¹ * q, r, by rwa [hdeg] at hr, ?_⟩
    have hinv : u * ↑hu.unit⁻¹ = 1 := hu.mul_val_inv
    rw [hPe]
    linear_combination hF - ((E : PowerSeries O) * q) * hinv
  have huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0 := by
    intro a q hq j
    have hr : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).degree
        < E.natDegree := by rw [hdeg]; exact Polynomial.degree_sum_fin_lt a
    have h0 := eq_zero_of_isDistinguishedAt_mul hI hE (q := u * q) hr (by
      rw [coe_sum_fin, hq, hPe]
      ring)
    have := coeff_sum_fin a j
    rw [h0, Polynomial.coeff_zero] at this
    exact this.symm
  have hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0 :=
    fun x hx => eq_zero_of_forall_pow_dvd hPnu hx
  constructor
  · intro a
    obtain ⟨α, hα⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull a
    refine ⟨α, hα.trans (Finset.sum_congr rfl fun t _ => ?_)⟩
    rw [hφ, itAlg_apply, mul_comm]
  · intro a' h t
    have h' : ∑ i, φ (a' i) * X ^ (i : ℕ) = 0 := by
      rw [← h]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hφ, itAlg_apply, mul_comm]
    ext m
    rw [map_zero]
    exact eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0 m a' h' t

end dvr

section ring
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem dvd_ell {ϖ : O} {ℓ e : ℕ} (he : 1 ≤ e) (h : Associated (ℓ : O) (ϖ ^ e)) : ϖ ∣ (ℓ : O) := by
  exact (dvd_pow_self ϖ (by omega)).trans h.symm.dvd

theorem ell_ne {ϖ : O} (hϖ : Irreducible ϖ) {ℓ e : ℕ} (h : Associated (ℓ : O) (ϖ ^ e)) :
    (ℓ : O) ≠ 0 := by
  exact h.ne_zero_iff.mpr (pow_ne_zero _ hϖ.ne_zero)

theorem ell_nonunit {ϖ : O} (hϖ : Irreducible ϖ) {ℓ e : ℕ} (he : 1 ≤ e)
    (h : Associated (ℓ : O) (ϖ ^ e)) : ¬ IsUnit (ℓ : O) := by
  exact fun hu => hϖ.not_isUnit (isUnit_of_dvd_unit (dvd_ell he h) hu)

theorem pshape' {B : Base O} {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e) (ell : ℕ) :
    B.PShape ell := by
  haveI := hB.complete
  exact pshape (ell_nonunit hϖ hB.one_le_e hB.assoc) hB.e3 (by have := hB.three_le; omega) ell

theorem unitDist {B : Base O} {ϖ : O} (hd : ϖ ∣ (B.ℓ : O)) {ell : ℕ} (hP : B.PShape ell) (s : ℕ)
    (hs : s < ell) : UnitDist ϖ (B.ℓ ^ s) (B.p s) := by
  obtain ⟨E, u, hm, hdeg, hdvd, -, hu, hp⟩ := hP s hs
  refine ⟨u, E, hu, { mem := fun {n} hn => ?_, monic := hm }, hdeg, hp⟩
  rw [Ideal.mem_span_singleton]
  exact hd.trans (hdvd n (hdeg ▸ hn))

theorem p_sub_mem {B : Base O} (h3 : B.E3) (hℓ : 2 ≤ B.ℓ) {s s' : ℕ} (hs : s < s') :
    ∃ d : PowerSeries O, B.p s' = d * B.p s + C (B.ℓ : O) := by
  obtain ⟨u, hu⟩ := h3
  have hit : ∀ k, (⇑B.φ)^[k + 1] X =
      (⇑B.φ)^[k] (u : PowerSeries O) * (⇑B.φ)^[k] X * (⇑B.φ)^[k] B.q ^ (B.ℓ - 1) := by
    intro k
    rw [Function.iterate_succ_apply, hu, ← itAlg_apply, map_mul, map_mul, map_pow, itAlg_apply,
      itAlg_apply, itAlg_apply]
  have hdiv : ∀ t, s + 1 ≤ t → B.p s ∣ (⇑B.φ)^[t] X := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      rw [hit s]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    | succ t _ ih =>
      rw [hit t]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _
  obtain ⟨d, hd⟩ := hdiv s' hs
  refine ⟨d, ?_⟩
  rw [p_eq B s', hd]
  ring

theorem coprimeRat_lt {B : Base O} {ϖ : O} {e : ℕ} (ha : Associated (B.ℓ : O) (ϖ ^ e)) (h3 : B.E3)
    (hℓ : 2 ≤ B.ℓ) {s s' : ℕ} (hs : s < s') :
    ∃ a a' : PowerSeries O, a * B.p s + a' * B.p s' = C (ϖ ^ e) := by
  obtain ⟨d, hd⟩ := p_sub_mem h3 hℓ hs
  obtain ⟨u, hu⟩ := ha
  refine ⟨-(C (u : O) * d), C (u : O), ?_⟩
  rw [← hu, map_mul, hd]
  ring

theorem constant_model_setting {B : Base O} {ϖ : O} {e : ℕ} (he : 1 ≤ e) (ha : Associated (B.ℓ : O) (ϖ ^ e))
    (h3 : B.E3) (hℓ : 2 ≤ B.ℓ) {ell : ℕ} (hP : B.PShape ell) : DistinguishedFamily ϖ B.ℓ ell B.p := by
  refine ⟨fun s hs => unitDist (dvd_ell he ha) hP s hs, fun s _ s' _ hne => ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨a, a', h'⟩ := coprimeRat_lt ha h3 hℓ h
    exact ⟨e, a, a', h'⟩
  · obtain ⟨a, a', h'⟩ := coprimeRat_lt ha h3 hℓ h
    exact ⟨e, a', a, by rw [add_comm]; exact h'⟩

theorem baseGood {B : Base O} {ϖ : O} {e : ℕ} (hB : PrimBase B ϖ e) {g hh : ℕ}
    (hg : g ≤ hh) (j : ℕ) : B.Good j (parM B.ℓ hh g) g := by
  have hM := lt_parM B.ℓ hh g (by have := hB.three_le; omega)
  exact base_ring_good_holds O B j _ g hB.e3 hB.e4 (le_of_lt (lt_of_le_of_lt (by omega) hM))

end ring

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  [NeZero n]

theorem latGood {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {Cu : Cuts n} {j g G hh sig ellmax : ℕ} (hN : PrimNum B.ℓ Cu j g G hh sig ellmax)
    {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] {L : Lat B n V}
    (hL : PrimLat L Cu j G hh) : L.Good Cu j (parM B.ℓ hh g) g sig := by
  classical
  have hd := dvd_ell hB.one_le_e hB.assoc
  obtain ⟨u₁, hu₁⟩ := one_add_unit_pow_formula O ϖ B hϖ hd hB.prime hB.three_le hB.e4
  have hM := lt_parM B.ℓ hh g (by have := hB.three_le; omega)
  let Mi : ZMod n → ℕ := fun i =>
    if ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n) then G else hh
  refine good_lattice_holds O ϖ B u₁ n Cu j (parM B.ℓ hh g) g G sig Mi V L hϖ hd
    (ell_ne hϖ hB.assoc) hB.prime hB.three_le hN.one_le_j hB.e3 hu₁ hN.G_le_g hN.sigOK hL.p9
    (fun i => ?_) (fun i => ?_) (fun c hc k hk1 hk2 => ?_) hL.pullFree
    (completion_holds O B n V L hB.complete hL.free) (X_regular_on_lattice O B n V L hL.free) hL.ltors
  · by_cases h : ∃ c ∈ Cu.cuts, ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i = c + (k : ZMod n)
    · simp only [Mi]
      rw [if_pos h]
      obtain ⟨c, hc, k, hk1, hk2, rfl⟩ := h
      exact hL.frobeniusBounded_after c hc k hk1 hk2
    · simp only [Mi]
      rw [if_neg h]
      exact hL.p5M i
  · have hGh : G ≤ hh := le_trans hN.G_le_g hN.g_le_h
    have hle : Mi i ≤ hh := by
      simp only [Mi]
      split_ifs <;> omega
    exact lt_of_le_of_lt hle (lt_of_le_of_lt (by omega) hM)
  · have h : ∃ c' ∈ Cu.cuts, ∃ k' : ℕ, 1 ≤ k' ∧ k' ≤ j ∧ c + (k : ZMod n) = c' + (k' : ZMod n) :=
      ⟨c, hc, k, hk1, hk2, rfl⟩
    simp only [Mi]
    rw [if_pos h]

theorem unit_phiIt {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀}
    {e₀ : V₀} (h : ∀ i, L₀.φ i e₀ = e₀) (i : ZMod n) (k : ℕ) (a : PowerSeries O) :
    L₀.phiIt i k (a • e₀) = (⇑B.φ)^[k] a • e₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    first
      | rw [Lat.phiIt, ih, L₀.φ_semi, h, Function.iterate_succ_apply']
      | (simp only [Lat.phiIt]
         rw [ih, L₀.φ_semi, h, Function.iterate_succ_apply'])

theorem unit_phiFree {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀} {e₀ : V₀}
    (hU : PrimUnit L₀ e₀) (i : ZMod n) (k : ℕ) : L₀.PhiFree i k := by
  haveI := hB.complete
  have hl := ell_nonunit hϖ hB.one_le_e hB.assoc
  have h1 : 1 ≤ B.ℓ := by have := hB.three_le; omega
  obtain ⟨hspan, hfree⟩ := basePhiFree hl hB.e3 h1 k
  refine ⟨B.ℓ ^ k, fun t => X ^ (t : ℕ), hspan, ?_⟩
  intro m hm hsum t
  have hm' : ∀ t, ∃ a : PowerSeries O, a • e₀ = m t := fun t => by
    have := hm t
    rwa [hU.N_eq i, Submodule.mem_span_singleton] at this
  choose a' ha' using hm'
  have hz : (∑ t : Fin (B.ℓ ^ k), X ^ (t : ℕ) * (⇑B.φ)^[k] (a' t)) • e₀ = 0 := by
    rw [Finset.sum_smul, ← hsum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← ha' t, unit_phiIt hU.φ_fix, mul_smul]
  have := hfree a' (hU.tors _ hz) t
  rw [← ha' t, this, zero_smul]

theorem unit_xReg {V₀ : Type} [AddCommGroup V₀] [Module (PowerSeries O) V₀] {L₀ : Lat B n V₀}
    {e₀ : V₀} (hU : PrimUnit L₀ e₀) : L₀.XReg := by
  intro i v hv hXv
  rw [hU.N_eq i, Submodule.mem_span_singleton] at hv
  obtain ⟨a, rfl⟩ := hv
  rw [smul_smul] at hXv
  rcases mul_eq_zero.mp (hU.tors _ hXv) with h | h
  · exact absurd h PowerSeries.X_ne_zero
  · rw [h, zero_smul]

theorem extGood {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {Cu : Cuts n} {j g G rr : ℕ} (hG : G ≤ g) (M : ℕ) {H : ZMod n → ℕ → ℕ}
    {V₂ V₀ : Type} [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] {L₂ : Lat B n V₂} {L₀ : Lat B n V₀} {e₀ : V₀}
    (hU : PrimUnit L₀ e₀) {Y : Ext L₂ L₀} (hY : PrimExt Y e₀ Cu j G rr H) :
    Y.Good e₀ Cu (LamOf B Cu H) j M g rr := by
  have hsat := saturation_first_form_holds O ϖ B j M g hϖ (dvd_ell hB.one_le_e hB.assoc) (ell_ne hϖ hB.assoc)
    hB.e3
  exact ⟨hY.lift, hY.p9, extension_complete_holds O B n V₂ V₀ L₂ L₀ Y hY.p6 (unit_xReg hU),
    fun c hc => lattice_induction_lemma_holds O B n j M g G Y.VY Y.LY c (by omega) (hY.frobeniusBounded_after c hc),
    fun c hc => saturation_holds_alt O B n j _ Y.VY Y.LY c hsat (hY.pullFree c hc),
    fun c hc => pullback_lemma_holds O B n Y.VY Y.LY c (Cu.ell c) (H c) (H c) (hY.frobeniusCobounded_arc c hc)
      (fun _ _ => le_rfl),
    fun c _ => extension_generated_holds O B n V₂ V₀ L₂ L₀ Y _ _ _ hY.p6 (unit_phiFree hϖ hB hU _ _)⟩

end lat

section arc
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Base O} {n : ℕ}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

theorem arcHyp {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} (hB : PrimBase B ϖ e)
    {h : LatHom L₁ L₂} {c : ZMod n} {ell ellmax : ℕ} (hell : ell ≤ ellmax) {H : ℕ → ℕ}
    {g sig rr kap : ℕ}
    (hA : PrimArc h c ell H g sig rr (parA sig rr g ellmax) kap ϖ) :
    ArcHyp h c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) g sig rr (parA sig rr g ellmax) kap ϖ := by
  obtain ⟨r₁, r₂, S₁, S₂, m, b, kind, U₁, U₂, PP, PP', hP⟩ := hA
  have hℓ : 2 ≤ B.ℓ := by have := hB.three_le; omega
  have hsh : B.PShape ell := pshape' hϖ hB ell
  have hMS : LevelModelSetting ϖ B.ℓ ell B.p H b kind U₁ U₂ :=
    ⟨hℓ, constant_model_setting hB.one_le_e hB.assoc hB.e3 hℓ hsh, hP.sat₁, hP.sat₂, hP.b_le_H⟩
  refine ⟨r₁, r₂, S₁, S₂, m, H, b, kind, U₁, U₂, PP, PP', rfl, hP.p4c₁, hP.p4c₂, hP.equiv₁,
    hP.equiv₂, hP.k2iii, hP.rd₁, hP.rd₂, hP.k3a2, hP.k3a4, hP.dcFix, hP.partner₁, hP.partner₂,
    hP.p3₁, hP.p3₂, hP.p4a₁, hP.p4a₂, hP.p4b₁, hP.p4b₂, hP.bridge₁, hP.bridge₂, hP.mapFl, hP.p4d,
    hP.ppval, hMS, hP.lLift, ?_⟩
  rcases hP.word with hW | hW | hW | hW | hW
  · exact Or.inl hW
  · exact Or.inr (Or.inl hW)
  · exact Or.inr (Or.inr (Or.inl hW))
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4⟩ := hW
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s₀, s₁, h0, h1, h2, h3, h4,
      (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).1⟩)))
  · obtain ⟨s₀, s₁, h0, h1, h2, h3, h4, h5, h6⟩ := hW
    have hb : 1 ≤ b s₀ := by
      have := hP.g_lt_b s₀ (by omega) (by rw [h3]; decide)
      omega
    have hle : 2 * sig + rr + 2 * g * ell ≤ parA sig rr g ellmax := by
      have := Nat.mul_le_mul_left (2 * g) hell
      unfold parA
      omega
    have hC : CLift B.ℓ (parA sig rr g ellmax) (U₁ s₁) (U₂ s₁) m.prL :=
      lemma_C_full_holds lemma_C_valuation_real O ϖ hϖ B e hB.one_le_e hB.assoc n V₁ V₂ L₁ L₂ h c ell _
        r₁ r₂ S₁ S₂ m H b kind U₁ U₂ g sig rr _ rfl hsh hMS hP.rd₁ hP.rd₂ hP.partner₁ hP.partner₂
        hP.p3₁ hP.p3₂ hP.p4a₁ hP.p4a₂ hP.bridge₁ hP.bridge₂ hP.flReg hP.mapFl hP.p4d s₀ s₁ h0 h1
        h2 h3 h4 (hP.cMap s₁ h1 h2) hle h6 h5
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s₀, s₁, h0, h1, h2, h3, h4, hC,
      (word_constants_holds O ϖ hϖ B.ℓ ell B.p b hℓ hMS.2.1 s₀ s₁ h0 h1).2 hb⟩)))

end arc

end Formalism.ExponentWindows.E.Prim

namespace Formalism.ExponentWindows.E

open PowerSeries

theorem theorem_E_primitive_form : ThmEPrim := by
  intro O _ _ _ ϖ hϖ B e n _ Cu H j g G hh sig rr kap ellmax V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h
    Zf₁ Zf₂ hB hN hL₁ hL₂ hU hBK hA κ hκ
  have hM1 : 1 ≤ parM B.ℓ hh g := by
    unfold parM
    exact Nat.le_add_left 1 _
  refine theorem_E_full_form O ϖ hϖ B n Cu (LamOf B Cu H) j (parM B.ℓ hh g) g sig rr
    (parA sig rr g ellmax) kap V₁ V₂ V₀ L₁ L₂ L₀ e₀ h Zf₁ Zf₂ hM1 (Prim.baseGood hB hN.g_le_h j)
    (Prim.latGood hϖ hB hN hL₁) (Prim.latGood hϖ hB hN hL₂) hN.j_le_ell hU.φ_fix hU.γ_fix
    hBK.smul hBK.rho (fun κ hκ => ?_) ?_ (fun c hc => ?_) κ hκ
  · obtain ⟨Y, hrep, hY⟩ := hBK.ext κ hκ
    exact ⟨Y, hrep, Prim.extGood hϖ hB hN.G_le_g _ hU hY⟩
  · unfold parA
    first
      | omega
      | nlinarith [Nat.zero_le (2 * g * ellmax)]
  · exact Prim.arcHyp hϖ hB (hN.ell_le c hc) (hA c hc)

end Formalism.ExponentWindows.E

namespace Formalism.ExponentWindows.E.Prim

open PowerSeries IdempotentNormalFormsRhoFacts GoodPlacesAlt

section p4
variable {O : Type} [CommRing O] {B : Base O}

theorem γ_sub_X (h4 : B.E4) (a : PowerSeries O) : ∃ c : PowerSeries O, B.γ a - a = X * c := by
  obtain ⟨e, he⟩ := h4
  obtain ⟨a', ha'⟩ : (X : PowerSeries O) ∣ a - C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]
    simp
  have ha : a = C (PowerSeries.constantCoeff a) + X * a' := by
    rw [← ha']
    ring
  have hC : B.γ (C (PowerSeries.constantCoeff a)) = C (PowerSeries.constantCoeff a) := by
    first
      | exact B.γ.commutes _
      | simpa [PowerSeries.algebraMap_eq] using B.γ.commutes (PowerSeries.constantCoeff a)
  refine ⟨(1 + (e : PowerSeries O) * B.q) * B.γ a' - a', ?_⟩
  have key : B.γ a - a = B.γ (C (PowerSeries.constantCoeff a) + X * a') -
      (C (PowerSeries.constantCoeff a) + X * a') := by
    rw [← ha]
  rw [key, map_add, map_mul, hC, he]
  ring

def GU (B : Base O) (x : PowerSeries O) : Prop := ∃ t : PowerSeries O, B.γ x = x * (1 + X * t)

theorem GU.one : GU B 1 := by
  exact ⟨0, by simp⟩

theorem GU.mul {x y : PowerSeries O} (hx : GU B x) (hy : GU B y) : GU B (x * y) := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨t', ht'⟩ := hy
  exact ⟨t + t' + X * t * t', by rw [map_mul, ht, ht']; ring⟩

theorem GU.pow {x : PowerSeries O} (hx : GU B x) (m : ℕ) : GU B (x ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact GU.one
  | succ m ih =>
    rw [pow_succ]
    exact ih.mul hx

variable {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]

theorem γ_pull_sub (L : Lat B n V) (h3 : B.E3) (h4 : B.E4) (h9 : L.P9) (i : ZMod n) (k : ℕ)
    {p : V} (hp : p ∈ L.pull i k) : L.γ (i + (k : ZMod n)) p - p ∈ sm X (L.pull i k) := by
  have hcommK : ∀ (k : ℕ) (v : V), L.γ (i + (k : ZMod n)) (L.phiIt i k v) = L.phiIt i k (L.γ i v) := by
    intro k v
    induction k with
    | zero => simp [Lat.phiIt]
    | succ k ih =>
      show L.γ (i + ((k + 1 : ℕ) : ZMod n)) (L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k v)) =
        L.φ (i + ((k + 1 : ℕ) : ZMod n)) (L.phiIt i k (L.γ i v))
      rw [← L.comm]
      have e : i + ((k + 1 : ℕ) : ZMod n) - 1 = i + (k : ZMod n) := by
        push_cast
        ring
      rw [e, ih]
  have hsub : ∀ (k : ℕ) (v w : V), L.phiIt i k (v - w) = L.phiIt i k v - L.phiIt i k w := by
    intro k v w
    induction k with
    | zero => rfl
    | succ k ih =>
      show L.φ _ (L.phiIt i k (v - w)) = L.φ _ (L.phiIt i k v) - L.φ _ (L.phiIt i k w)
      rw [ih, map_sub]
  have hsmul : ∀ (k : ℕ) (a : PowerSeries O) (v : V), L.phiIt i k (a • v) = (⇑B.φ)^[k] a • L.phiIt i k v := by
    intro k a v
    induction k with
    | zero => rfl
    | succ k ih =>
      show L.φ _ (L.phiIt i k (a • v)) = _ • L.φ _ (L.phiIt i k v)
      rw [ih, L.φ_semi, Function.iterate_succ_apply']
  have hXdiv : ∀ k : ℕ, ∃ d : PowerSeries O, (⇑B.φ)^[k] X = X * d := by
    obtain ⟨u, hu⟩ := h3
    intro k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨(u : PowerSeries O) * B.q ^ (B.ℓ - 1) * B.φ d, ?_⟩
      rw [Function.iterate_succ_apply', hd, map_mul, hu]
      ring
  have hsmX : ∀ z ∈ L.pull i k, X • z ∈ sm X (L.pull i k) := fun z hz => by
    unfold sm
    exact Submodule.mem_map.2 ⟨z, hz, LinearMap.lsmul_apply _ _⟩
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.1 (h9 i v hv)
    rw [hcommK, ← hsub, ← hwe, LinearMap.lsmul_apply, hsmul]
    obtain ⟨d, hd⟩ := hXdiv k
    rw [hd, mul_smul]
    exact hsmX _ ((L.pull i k).smul_mem d (Submodule.subset_span ⟨w, hw, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, show L.γ (i + (k : ZMod n)) x + L.γ (i + (k : ZMod n)) y - (x + y) =
      (L.γ (i + (k : ZMod n)) x - x) + (L.γ (i + (k : ZMod n)) y - y) by abel]
    exact (sm X (L.pull i k)).add_mem hx hy
  | smul a x hxs hx =>
    rw [L.γ_semi]
    obtain ⟨c, hc⟩ := γ_sub_X h4 a
    have e : B.γ a • L.γ (i + (k : ZMod n)) x - a • x =
        B.γ a • (L.γ (i + (k : ZMod n)) x - x) + (X : PowerSeries O) • (c • x) := by
      rw [smul_sub, smul_smul, ← hc, sub_smul]
      abel
    rw [e]
    exact (sm X (L.pull i k)).add_mem ((sm X (L.pull i k)).smul_mem (B.γ a) hx)
      (hsmX _ ((L.pull i k).smul_mem c hxs))

end p4

end Formalism.ExponentWindows.E.Prim

namespace Formalism.ExponentWindows.E

open PowerSeries IdempotentNormalFormsRhoFacts

theorem partner_fourth_fourth_form : LiftsDivisibleOf := by
  intro O _ B n V₁ V₂ _ _ _ _ L₁ L₂ h c ell g rr hI₁ hI₂ hW x hx
  set T := B.Th ell g with hT
  have hx' : T • x ∈ L₂.N c := hx
  obtain ⟨y, hy, hfy⟩ := hW _ hx'
  obtain ⟨x₁, hx₁⟩ := hI₁.2 y
  have hx₁' : T • x₁ = y := hx₁
  subst hx₁'
  refine ⟨x₁, hy, ?_⟩
  apply hI₂.1
  show T • h.f x₁ = T • (B.lc ^ rr • x)
  rw [← map_smul, hfy, smul_comm]

end Formalism.ExponentWindows.E
end
