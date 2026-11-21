import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NGDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.ValOneOfNotMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs

section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem flag_gram {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (a b : Fin (r + 1)) :
    S.hT (F.fvec a) (F.fvec b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_norm]
    | cast j =>
      have h := S.herm.eq (F.e j) F.z
      rw [F.z_orth, map_zero] at h
      simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
      rw [← h]
      simp [Fin.castSucc_ne_last]
  | cast i =>
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
    | cast j => simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]

theorem frameAct_one {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {n : ℕ}
    (f : Fin n → S.V) : frameAct f (1 : Matrix (Fin n) (Fin n) (𝓞 E)) = f := by
  funext b
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [Matrix.one_apply_ne hc]
  · simp

theorem star_eq_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) : star x = D.conjF x := by
  rw [D.conjF_eq]
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ x).symm

theorem one_mem_dd (D : Formalism.BasicNotions.D7) (k : ℕ) :
    (1 : D.host.E) ∈ ((ddS D) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ddS D ≠ 0 := by
    unfold ddS
    rw [FractionalIdeal.coeIdeal_ne_zero]
    exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot)
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have hk0 : ddS D ^ k ≠ 0 := pow_ne_zero _ h0
  have hk1 : ddS D ^ k ≤ 1 := pow_le_one' hle k
  rw [zpow_neg, zpow_natCast]
  have h1 := FractionalIdeal.inv_anti_mono hk0 one_ne_zero hk1
  rw [inv_one] at h1
  exact h1 (FractionalIdeal.one_mem_one _)

theorem pair_int (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ)
    {x y : (VS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y := by
  have hd : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU]; exact hy
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hd
  rw [Submodule.mem_iInf] at hd
  have hd2 := hd x
  rw [Submodule.mem_iInf] at hd2
  have hint := hd2 hx
  rw [Submodule.mem_comap] at hint
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hint
  simp only [LinearMap.coe_restrictScalars] at ho
  exact ⟨o, ho⟩

theorem modG_at (D : Formalism.BasicNotions.D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {y : (VS D).V}
    (h : ModG (VS D) Λ (gS D) y) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ l ∈ Λ, (s : D.host.E) • y = ((gS D : ℕ) : D.host.E) • l := by
  obtain ⟨s, hs, hsy⟩ := h P hP
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsy
  obtain ⟨l, hl, hl'⟩ := hsy
  refine ⟨s, hs, l, hl, ?_⟩
  rw [algebraMap_smul, ← hl', ← algebraMap_smul (A := D.host.E) ((gS D : ℕ) : 𝓞 D.host.E) l]
  simp

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def sg1 (p : PlF D) (g : Loc.SplitG (M p).L) : D.host.E →+* (D.s.atP p).Fp :=
  (RingHom.fst _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE)

def sg2 (p : PlF D) (g : Loc.SplitG (M p).L) : D.host.E →+* (D.s.atP p).Fp :=
  (RingHom.snd _ _).comp (g.e.toRingEquiv.toRingHom.comp (D.s.atP p).ιE)

theorem firstSplitEmbed_apply (p : PlF D) (g : Loc.SplitG (M p).L) (x : D.host.E) :
    sg1 p g x = (g.e ((D.s.atP p).ιE x)).1 := rfl

theorem secondSplitEmbed_apply (p : PlF D) (g : Loc.SplitG (M p).L) (x : D.host.E) :
    sg2 p g x = (g.e ((D.s.atP p).ιE x)).2 := rfl

theorem firstSplitEmbed_star (δ : ∀ p : PlF D, (D.s.atP p).Fp) (hA : ∀ p, Agree δ M p) (p : PlF D) (g : Loc.SplitG (M p).L)
    (x : D.host.E) : sg1 p g (star x) = sg2 p g x := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  rw [firstSplitEmbed_apply, secondSplitEmbed_apply, star_eq_conjF]
  have h1 : (D.s.atP p).ιE (D.conjF x) = (D.s.atP p).cj ((D.s.atP p).ιE x) := ((D.s.atP p).cj_ιE x).symm
  rw [h1, ← hcj, g.e_cj]
  rfl

theorem split_ell (δ : ∀ p : PlF D, (D.s.atP p).Fp) (hA : ∀ p, Agree δ M p) (p : PlF D) (g : Loc.SplitG (M p).L)
    (hs : (M p).split = some g) :
    (g.q : (D.s.atP p).Fp) = ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ∧
      Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  have hm := (hA p).2.2.2.2.2
  rw [hs] at hm
  rcases hsp : (D.s.atP p).split with _ | sg
  · rw [hsp] at hm
    exact hm.elim
  · rw [hsp] at hm
    have hqq : g.q = sg.q := hm.2
    refine ⟨by rw [hqq, sg.q_eq], (D.s_split p).1 (by rw [hsp]; rfl)⟩

theorem val_q_lt (p : PlF D) (g : Loc.SplitG (M p).L) :
    valuation (D.s.atP p).Fp (g.q : (D.s.atP p).Fp) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 g.q_irr.not_isUnit

theorem gS_split (p : PlF D) (h : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)) :
    ∃ k : ℕ, gS D = Loc.resChar p * k := by
  unfold gS
  rcases Finset.mem_insert.1 h with h0 | h1
  · exact ⟨D.host.g 1, by rw [h0]⟩
  · exact ⟨D.host.g 0, by rw [Finset.mem_singleton.1 h1, mul_comm]⟩

theorem cong_one {K : Type} [Field K] [ValuativeRel K] (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ) {x y : (VS D).V} (hx : x ∈ Λ) (hy : ModG (VS D) Λ (gS D) y)
    (σ : D.host.E →+* K) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hPσ : ∀ s : 𝓞 D.host.E, s ∉ P.asIdeal → valuation K (σ (s : D.host.E)) = 1) (q m : 𝒪[K])
    (hg : ((gS D : ℕ) : K) = (q : K) * m) : ∃ t : 𝒪[K], σ ((VS D).hT x y) = (q : K) * t := by
  obtain ⟨s, hs, l, hl, hsl⟩ := modG_at D Λ hy P hgP
  obtain ⟨o, ho⟩ := pair_int D Λ hU hx hl
  have he : (s : D.host.E) * (VS D).hT x y = ((gS D : ℕ) : D.host.E) * o := by
    rw [ho, ← smul_eq_mul, ← map_smul, hsl, map_smul, smul_eq_mul]
  obtain ⟨t, ht⟩ := div_q σ q m 1 (gS D) (s : D.host.E) _ o (hPσ s hs) (by rw [pow_one]; exact hg) he
  exact ⟨t, by rw [ht, pow_one]⟩

theorem cong_two {K : Type} [Field K] [ValuativeRel K] (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hU : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ) {y y' : (VS D).V} (hy : ModG (VS D) Λ (gS D) y)
    (hy' : ModG (VS D) Λ (gS D) y') (σ : D.host.E →+* K) (P P' : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hgP' : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal)
    (hPσ : ∀ s : 𝓞 D.host.E, s ∉ P.asIdeal → valuation K (σ (s : D.host.E)) = 1)
    (hP'σ : ∀ s : 𝓞 D.host.E, s ∉ P'.asIdeal → valuation K (σ (star (s : D.host.E))) = 1) (q m : 𝒪[K])
    (hg : ((gS D : ℕ) : K) = (q : K) * m) : ∃ t : 𝒪[K], σ ((VS D).hT y y') = (q : K) ^ 2 * t := by
  obtain ⟨s, hs, l, hl, hsl⟩ := modG_at D Λ hy P' hgP'
  obtain ⟨s', hs', l', hl', hsl'⟩ := modG_at D Λ hy' P hgP
  obtain ⟨o, ho⟩ := pair_int D Λ hU hl hl'
  have he : (star (s : D.host.E) * s') * (VS D).hT y y' = ((gS D ^ 2 : ℕ) : D.host.E) * o := by
    have h1 : (VS D).hT ((s : D.host.E) • y) ((s' : D.host.E) • y') = star (s : D.host.E) * s' * (VS D).hT y y' := by
      rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
      ring
    have h2 : (VS D).hT (((gS D : ℕ) : D.host.E) • l) (((gS D : ℕ) : D.host.E) • l') =
        ((gS D ^ 2 : ℕ) : D.host.E) * (VS D).hT l l' := by
      rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply,
        star_natCast]
      push_cast
      ring
    rw [← h1, hsl, hsl', h2, ho]
  have hc : valuation K (σ (star (s : D.host.E) * s')) = 1 := by
    rw [map_mul, Valuation.map_mul, hP'σ s hs, hPσ s' hs', one_mul]
  obtain ⟨t, ht⟩ := div_q σ q (m ^ 2) 2 (gS D ^ 2) _ _ o hc (by push_cast; rw [hg]; ring) he
  exact ⟨t, ht⟩

theorem fin_three {E K : Type} [Field E] [Field K] (σ : E →+* K) (A B C : E) (T T' : ℕ) (c : Prop) [Decidable c]
    (hA : A = if c then -(T : E) else 0) (hB : B = if c then -(T' : E) else 0) (x : K) (hx : σ C = x) :
    σ (A + B - C) + (if c then (T : K) + (T' : K) else 0) = -x := by
  rw [map_sub, map_add, hx, hA, hB]
  split_ifs
  · rw [map_neg, map_neg, map_natCast, map_natCast]
    ring
  · rw [map_zero]
    ring


end PI.CntNotIntW
end
end

section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiffG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : PlF D), (D.s.atP p).split.isSome → ∀ t : D.host.F,
    (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) → (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp]

def DeltaInvG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g → (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

theorem split_isSome {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (p : PlF D)
    (g : Loc.SplitG (M p).L) (hs : (M p).split = some g) : (D.s.atP p).split.isSome := by
  have h := (hA p).2.2.2.2.2
  rw [hs] at h
  cases hsp : (D.s.atP p).split with
  | none => rw [hsp] at h; exact h.elim
  | some sg => rfl

theorem deltaInvG_of (hL : LocDiff) (hD : DiffG) : DeltaInvG := by
  intro D δ M hA p g hs
  obtain ⟨t, ht, hne, -, hinv⟩ := hL D δ M hA p
  have hti : (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] := hD D p (split_isSome hA p g hs) t ht
  have hι : (D.s.atP p).ιF t ≠ 0 := by
    intro h0; apply hne; rw [h0, mul_zero]
  have e : (δ p)⁻¹ = (D.s.atP p).ιF t * (δ p * (D.s.atP p).ιF t)⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hι, mul_one]
  rw [e]
  exact mul_mem hti hinv

theorem gS_gpart (D : Formalism.BasicNotions.D7) (p : PlF D) : ∃ k : ℕ, gS D = gpart p * k := by
  unfold Formalism.MainNotions.S.LocalSplitGroups.gpart Formalism.MainNotions.S.Lat.gS
  split_ifs
  · exact ⟨D.host.g 1, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩
  · exact ⟨D.host.g 0 * D.host.g 1, (one_mul _).symm⟩

theorem ringInverse_eq {R : Type*} [MonoidWithZero R] (x y : R) (hxy : x * y = 1) (hu : IsUnit x) : Ring.inverse x = y := by
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [hxy, mul_one]
    _ = Ring.inverse x * x * y := by rw [mul_assoc]
    _ = y := by rw [Ring.inverse_mul_cancel x hu, one_mul]

theorem frIntG_of_delta (hΔ : DeltaInvG) : FrIntG := by
  intro D δ M hA p g hs a
  have hδi : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := hΔ D δ M hA p g hs
  have hδ0 : δ p ≠ 0 := (hA p).2.1
  obtain ⟨k, hk⟩ := gS_gpart D p
  unfold Formalism.MainNotions.S.LocalSplitGroups.frFac
  by_cases h0 : Formalism.MainNotions.S.Lat.gS D = 0
  · have hu : ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 0 := by
      simp [Formalism.MainNotions.S.LocalSplitGroups.uP, h0]
    rw [hu, map_zero, mul_zero]
    rcases Nat.eq_zero_or_pos (D.R.rS - a.val) with hm0 | hm0
    · rw [hm0, pow_zero, Ring.inverse_one, map_one]
      exact one_mem _
    · rw [zero_pow hm0.ne', Ring.inverse_zero, map_zero]
      exact zero_mem _
  · have hk0 : k ≠ 0 := by
      rintro rfl; rw [mul_zero] at hk; exact h0 hk
    have hgp : Formalism.MainNotions.S.LocalSplitGroups.gpart p ≠ 0 := by
      intro hg; rw [hg, zero_mul] at hk; exact h0 hk
    have huQ : (k : ℚ) * Formalism.MainNotions.S.LocalSplitGroups.uP p = 1 := by
      simp only [Formalism.MainNotions.S.LocalSplitGroups.uP, hk]
      push_cast
      field_simp
    have hu : (k : D.host.E) * ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) = 1 := by
      have h1 := congrArg (fun q : ℚ => (q : D.host.E)) huQ
      push_cast at h1
      exact h1
    have hbase : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
        (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp)) = 1 := by
      rw [mul_right_comm, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hδ0, one_mul, map_natCast,
        ← map_natCast (D.s.atP p).ιE k, ← map_mul, hu, map_one]
    have hXY : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
        (D.s.atP p).ιE ((Formalism.MainNotions.S.LocalSplitGroups.uP p : ℚ) : D.host.E)) ^ (D.R.rS - a.val) *
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((δ p)⁻¹ * (k : (D.s.atP p).Fp))) ^ (D.R.rS - a.val) = 1 := by
      rw [← mul_pow, hbase, one_pow]
    rw [ringInverse_eq _ _ hXY (Units.mkOfMulEqOne _ _ hXY).isUnit]
    simp only [map_pow, AlgEquiv.commutes, Prod.pow_fst, Prod.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact pow_mem (mul_mem hδi (natCast_mem _ k)) _

theorem frIntG_of (hL : LocDiff) (hD : DiffG) : FrIntG := frIntG_of_delta (deltaInvG_of hL hD)

end PI.CntNotIntW
end
end

section
noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

variable {D : Formalism.BasicNotions.D7}

theorem ell_mem (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  unfold Loc.resChar
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem vle_iff (p : PlF D) (x y : D.host.F) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF x) ≤ valuation (D.s.atP p).Fp ((D.s.atP p).ιF y) ↔
      p.valuation D.host.F x ≤ p.valuation D.host.F y := by
  rw [← (D.s.atP p).val x y]
  exact (Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).symm

theorem val_one_of_notMem (p : PlF D) (d : 𝓞 D.host.F) (hd : d ∉ p.asIdeal) :
    valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F d)) = 1 := by
  have h1 : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F d) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h1' : p.valuation D.host.F 1 = 1 := map_one _
  apply le_antisymm
  · have h2 := (vle_iff p (algebraMap (𝓞 D.host.F) D.host.F d) 1).2 (by rw [h1, h1'])
    simpa only [map_one] using h2
  · have h2 := (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F d)).2 (by rw [h1, h1'])
    simpa only [map_one] using h2

theorem ell_not_mem_sq (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2 := by
  intro hmem
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hx1 : ¬ (p.valuation D.host.F 1 ≤ p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F π)) := by
    rw [map_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    norm_num
  have hxlt : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) < 1 := by
    have h1 := mt (vle_iff p 1 (algebraMap (𝓞 D.host.F) D.host.F π)).1 hx1
    simp only [map_one] at h1
    exact not_le.1 h1
  have hvl : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F ((Loc.resChar p : ℕ) : 𝓞 D.host.F)) ≤
      p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (π ^ 2)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_pow, hπ, ← WithZero.exp_nsmul]
    have h2 := (p.intValuation_le_pow_iff_mem _ 2).2 hmem
    convert h2 using 2 <;> norm_num
  have hq : valuation (D.s.atP p).Fp (sg.q : (D.s.atP p).Fp) ≤
      valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2 := by
    have h1 := (vle_iff p _ _).2 hvl
    simp only [map_natCast, map_pow] at h1
    rw [sg.q_eq]
    exact h1
  have hxmem : (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) ∈ 𝒪[(D.s.atP p).Fp] :=
    (Valuation.mem_integer_iff _ _).2 hxlt.le
  have hI := Valuation.integer.integers (valuation (D.s.atP p).Fp)
  have hdvd : (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) ^ 2 ∣ sg.q := by
    apply hI.dvd_of_le
    change valuation _ (sg.q : (D.s.atP p).Fp) ≤
      valuation _ (((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π)) ^ 2)
    rw [map_pow]
    exact hq
  obtain ⟨c, hc⟩ := hdvd
  have hsplit : sg.q = (⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * ((⟨_, hxmem⟩ : 𝒪[(D.s.atP p).Fp]) * c) := by
    rw [hc]
    ring
  rcases sg.q_irr.isUnit_or_isUnit hsplit with hu | hu
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    exact (ne_of_lt hxlt) h1
  · have h1 := hI.isUnit_iff_valuation_eq_one.1 hu
    have h2 : valuation (D.s.atP p).Fp
        ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π) * (c : (D.s.atP p).Fp)) = 1 := h1
    rw [map_mul] at h2
    have hc1 : valuation (D.s.atP p).Fp (c : (D.s.atP p).Fp) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
    have h5 := mul_le_of_le_one_right'
      (a := valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F π))) hc1
    rw [h2] at h5
    exact absurd hxlt (not_lt.2 h5)

theorem not_dvd_diff (p : PlF D)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p)) :
    ¬ p.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  haveI hℓ : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
  have hmem := ell_mem p
  have hsq := ell_not_mem_sq p sg
  have hle : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 hmem
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hle
  haveI hPm : p.asIdeal.IsMaximal := p.isMaximal
  have hcop : IsCoprime p.asIdeal Q := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have h1 : p.asIdeal = p.asIdeal ⊔ Q := Ideal.IsMaximal.eq_of_le hPm hne le_sup_left
    have h2 : Q ≤ p.asIdeal := by
      rw [h1]
      exact le_sup_right
    apply hsq
    have h3 : Ideal.span {((Loc.resChar p : ℕ) : 𝓞 D.host.F)} ≤ p.asIdeal ^ 2 := by
      rw [hQ, sq]
      exact Ideal.mul_mono_right h2
    exact (Ideal.span_singleton_le_iff_mem _).1 h3
  have hmap : p.asIdeal * Q =
      Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hQ]
  haveI : (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hℓ.out).irreducible
  haveI : NeZero (Loc.resChar p) := ⟨hℓ.out.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((Loc.resChar p : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (Loc.resChar p)).symm.toEquiv
  exact not_dvd_differentIdeal_of_isCoprime ℤ (p := Ideal.span {((Loc.resChar p : ℕ) : ℤ)})
    p.asIdeal Q hcop hmap

theorem different_lattice_index : DiffG := by
  intro D p hs t ht
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hs
  have hnd := not_dvd_diff (D := D) p sg
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨d, hdD, hdp⟩ := SetLike.not_le_iff_exists.1 hnd
  have hdt : ∃ b : 𝓞 D.host.F,
      algebraMap (𝓞 D.host.F) D.host.F b = algebraMap (𝓞 D.host.F) D.host.F d * t := by
    have h1 : algebraMap (𝓞 D.host.F) D.host.F d ∈
        (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F)) := by
      rw [← coeSubmodule_differentIdeal ℤ ℚ (𝓞 D.host.F)]
      exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hdD, rfl⟩
    have h2 : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 D.host.F) D.host.F) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := ht b
      rw [Algebra.traceForm_apply]
      exact RingHom.mem_range.2 ⟨n, by simpa using hn.symm⟩
    have h3 := (Submodule.mem_div_iff_forall_mul_mem.1 h1) t h2
    exact Submodule.mem_one.1 h3
  obtain ⟨b, hb⟩ := hdt
  have hv := val_one_of_notMem (D := D) p d hdp
  have hb1 : valuation (D.s.atP p).Fp ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F b)) ≤ 1 := by
    have h4 := (vle_iff (D := D) p (algebraMap (𝓞 D.host.F) D.host.F b) 1).2
      (by rw [map_one]; exact p.valuation_le_one b)
    simpa only [map_one] using h4
  rw [hb, map_mul, map_mul, hv, one_mul] at hb1
  exact (Valuation.mem_integer_iff _ _).2 hb1

end PI.CntNotIntW
end
end

section
namespace PI.CntNotIntW



end PI.CntNotIntW
end
