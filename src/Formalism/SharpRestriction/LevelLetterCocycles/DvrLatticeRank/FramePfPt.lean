import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Coeff

variable {R : Type} [CommRing R]

theorem framepf_coeff_pow_lt (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m j : ℕ)
    (hj : j < m) : PowerSeries.coeff j (f ^ m) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem framepf_coeff_pow_self (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = PowerSeries.coeff 1 f ^ m := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem framepf_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem framepf_levB_gam (hc : IsCrys PD T.ρ) (g : W.Gam)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - 1)) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Ct.levB T i 1 ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Ct.levB T i 1 x k :=
  Ct.levB_Γ T hc g i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) (by simpa using hv) (by simp) x hx k

theorem framepf_levB_zero (hc : IsCrys PD T.ρ) (i : ZMod n)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (a : LetA O n) (R : ℕ) (ha : ∀ j < R, PowerSeries.coeff j (W.lev i 1 a) = 0)
    (x w : ↥(W.N T)) (hxw : W.γD T W.gam (x : W.DD T) - x = a • (w : W.DD T))
    (hw : ∀ r : ℤ, r < 0 → W.levN T i 1 w r = 0) (r : ℤ) (h1 : 1 ≤ r) (hR : r < R) :
    Ct.levB T i 1 x r = 0 := by
  have hx : W.γD T W.gam (x : W.DD T) ∈ W.N T := W.N_Γ T W.gam x x.2
  have haw : a • (w : W.DD T) ∈ W.N T := (W.N T).smul_mem a w.2
  have hsub : (⟨_, hx⟩ : ↥(W.N T)) - x = ⟨_, haw⟩ := Subtype.ext (by simp [hxw])
  have hlev := congrArg (fun y => Ct.levB T i 1 y r) hsub
  simp only [map_sub, Pi.sub_apply] at hlev
  rw [framepf_levB_gam Ct T hc W.gam hv i x hx r] at hlev
  have hzero : Ct.levB T i 1 ⟨_, haw⟩ r = 0 := by
    refine framepf_ιV_inj (PD := PD) T ?_
    rw [map_zero, ← Ct.levN_eq]
    have : (⟨_, haw⟩ : ↥(W.N T)) = a • w := rfl
    rw [this, W.levN_smul]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < R
    · rw [ha j hj, zero_smul]
    · simp only [hw (r - (j : ℤ)) (by omega), smul_zero]
  rw [hzero] at hlev
  have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ r - 1) • Ct.levB T i 1 x r = 0 := by
    rw [sub_smul, one_smul]; exact hlev
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hχ r h1))

theorem framepf_levB_phi (hc : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hQ : ∀ j < m, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (i - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    Ct.levB T i ζ ⟨_, hm⟩ k =
      serC (W.lev i ζ (W.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (i - 1) 1 x 0)) k := by
  rw [Ct.levB_φ T hc i ζ hζ x m hm k, hζ1]
  unfold serC
  split_ifs with hk0
  · rw [finsum_eq_single _ k.toNat]
    · have : k - (k.toNat : ℤ) = 0 := by omega
      rw [this, zpow_zero, one_smul]
    · intro j hj
      by_cases hjm : j < m
      · rw [hQ j hjm, zero_smul]
      · by_cases hjk : (j : ℤ) < k
        · rw [hmid (k - (j : ℤ)) (by omega) (by omega), map_zero, smul_zero, smul_zero]
        · have : (j : ℤ) ≠ k := fun h => hj (by omega)
          rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]

theorem framepf_valAt (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hex : ∃ k : ℕ, W.Q ^ k • W.φD T (x : W.DD T) ∈ W.N T) :
    valAt W T c ζ (x : W.DD T) = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := by
  classical
  unfold valAt
  rw [dif_pos hex]
  have hm := Nat.find_spec hex
  have hC := framepf_levB_phi Ct T hc c ζ hζ hζ1 x (Nat.find hex) 1 hm
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg
    (fun r h1 h2 => by omega) (Nat.find hex : ℤ) (by omega)
  rw [Ct.levN_eq, hC]
  unfold serC
  rw [if_pos (by omega), map_smul, map_pow, Int.toNat_natCast, framepf_coeff_pow_self _ hQ0, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hQ1), one_smul]

theorem framepf_levN_phi (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (c - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    W.levN T c ζ ⟨_, hm⟩ k = serC (W.lev c ζ (W.Q ^ m)) (valAt W T c ζ (x : W.DD T)) k := by
  rw [framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x hneg ⟨m, hm⟩, Ct.levN_eq,
    framepf_levB_phi Ct T hc c ζ hζ hζ1 x m R hm
      (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg hmid k hk]
  unfold serC
  split_ifs
  · rw [map_smul]
  · rw [map_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
end

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Zero

open PowerSeries

variable {LL : Type} [Field LL]

theorem framepf_exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative LL E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  have hX1 : X ∣ E - 1 := by
    rw [PowerSeries.X_dvd_iff]
    simp [h0]
  obtain ⟨w1, hw1⟩ := hX1
  have hc1 : constantCoeff w1 = 1 := by
    have h2 : coeff 0 (PowerSeries.derivative LL E) = coeff 1 E := by
      rw [PowerSeries.coeff_derivative]
      simp
    rw [hd] at h2
    have h1 : coeff 1 (E - 1) = coeff 0 w1 := by
      rw [hw1]
      exact PowerSeries.coeff_succ_X_mul 0 w1
    have h3 : coeff 1 (E - 1) = coeff 1 E := by
      simp [PowerSeries.coeff_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1, h3, ← h2,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  induction p with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hwc⟩ := ih
    refine ⟨w * E + w1, ?_, ?_⟩
    · have he : E ^ (k + 1) - 1 = (E ^ k - 1) * E + (E - 1) := by ring
      rw [he, hw, hw1]
      ring
    · simp [hwc, hc1, h0]

end Zero

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

open PowerSeries in

theorem framepf_lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  obtain ⟨w, hw, hwc⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hp1 : PD.p ≠ 1 := by
    intro h
    have h1 := W.v_l
    rw [h, Nat.cast_one, AddValuation.map_one] at h1
    simp at h1
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h2 := hζ.eq_orderOf
    rw [h, orderOf_one] at h2
    exact hp1 h2
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hfq : W.lev c ζ letπ * W.lev c ζ W.q = E ^ PD.p - 1 := by
    rw [← map_mul, hq, map_sub, map_pow, map_add, map_one, hE, mul_pow, ← map_pow, hζp, map_one,
      one_mul]
  set P := W.lev c ζ letπ with hPdef
  have hP : P = C ζ * E - 1 := eq_sub_of_add_eq' hE
  have hPc : constantCoeff P = ζ - 1 := by
    rw [hP]
    simp [hE0]
  have hPne : constantCoeff P ≠ 0 := by
    rw [hPc]
    exact sub_ne_zero.mpr hζ1
  refine ⟨w * P⁻¹, ?_, ?_⟩
  · have hinv : P⁻¹ * P = 1 := PowerSeries.inv_mul_cancel P hPne
    calc W.lev c ζ W.q = (P⁻¹ * P) * W.lev c ζ W.q := by rw [hinv, one_mul]
      _ = P⁻¹ * (E ^ PD.p - 1) := by rw [mul_assoc, hfq]
      _ = X * (w * P⁻¹) := by rw [hw]; ring
  · rw [map_mul, hwc, PowerSeries.constantCoeff_inv, hPc]
    exact mul_ne_zero hp0 (inv_ne_zero (sub_ne_zero.mpr hζ1))

theorem framepf_Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [Formalism.BasicNotions.LocWach.Q, hs]

theorem framepf_Q_at (hs : W.s = 1) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  rw [framepf_Q_eq_q W hs, hu]
  refine ⟨by simp, ?_⟩
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * u) = PowerSeries.coeff 0 u :=
    PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu0

end Local

theorem framepf_pt_prim (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : IsPrimitiveRoot ζ l := by
  obtain ⟨τs, ⟨-, hroot⟩, -⟩ := hpt
  have hpow : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rwa [zero_add, (D.loc l).ζQ_zero] at h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show _ ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    refine (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _) ?_
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one]
    exact hpow
  set y : Ks K 1 := ⟨_, hmem⟩ with hydef
  have hyζ : τs y = ζ := hroot y rfl
  have hy1 : y ^ l = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hpow
  have hy2 : y ≠ 1 := by
    intro h
    apply (D.loc l).ζQ_one
    have h' := congrArg Subtype.val h
    exact h'
  have hprim : IsPrimitiveRoot y l := by
    have ho := orderOf_eq_prime hy1 hy2
    have h0 := IsPrimitiveRoot.orderOf y
    rwa [ho] at h0
  rw [← hyζ]
  exact hprim.map_of_injective τs.injective

end Formalism.MainNotions.N.Ln34

end
end
