import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledPeriodPairInvariants
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HcfjHolds

section
section
open GlobalTheory.Published Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem isIntegral_sqrtNegNat (p : ℕ) : IsIntegral ℤ (sqrtNegNat p) :=
  IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)

theorem exists_rat_of_mem_adjoin_sqrtNegNat {p : ℕ} {z : ℂ} (hz : z ∈ ℚ⟮sqrtNegNat p⟯) :
    ∃ a b : ℚ, z = a + b * sqrtNegNat p := by
  have hint : IsIntegral ℚ (sqrtNegNat p) := (isIntegral_sqrtNegNat p).tower_top
  have hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - p * (b * d), a * d + b * c, by
      push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩

theorem dvd_of_sqrtNegNat_mem {p q : ℕ} (hp : p.Prime) (h : sqrtNegNat q ∈ ℚ⟮sqrtNegNat p⟯) :
    p ∣ q := by
  obtain ⟨a, b, e⟩ := exists_rat_of_mem_adjoin_sqrtNegNat h
  have ha : a = 0 := by
    have := congrArg Complex.re e
    simpa [sqrtNegNat] using this.symm
  have e2 : (q : ℂ) = b ^ 2 * p := by
    have := sqrtNegNat_sq q
    rw [e, ha] at this
    push_cast at this
    linear_combination this - (b : ℂ) ^ 2 * sqrtNegNat_sq p
  have e3 : (q : ℚ) = b ^ 2 * p := by exact_mod_cast e2
  have hs : IsSquare ((q * p : ℕ) : ℚ) := ⟨b * p, by push_cast; rw [e3]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.1 hs
  have hpn : p ∣ n := by
    have : p ∣ n * n := hn ▸ dvd_mul_left p q
    exact (hp.dvd_mul.1 this).elim id id
  have : p * p ∣ q * p := hn ▸ mul_dvd_mul hpn hpn
  exact Nat.dvd_of_mul_dvd_mul_right hp.pos this

theorem mem_adjoin_of_invariant {p : ℕ} {L : PeriodPair} (hL : IsIntegersLattice p L) (m : ℂ) (hm0 : m ≠ 0)
    (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) : m ∈ ℚ⟮sqrtNegNat p⟯ := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)
  rw [e, mul_one] at this
  exact ((hL m).1 this).1

theorem integersLattice_invariants_ne_zero :
    ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L →
      L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  intro p L hp h3 hL
  refine ⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩
  · have hs := sqrtNegNat_sq 3
    push_cast at hs
    have h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1 := by
      linear_combination (3 / 8 + sqrtNegNat 3 / 8) * hs
    have hm := mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2)
      (fun e => by rw [e] at h6; norm_num at h6) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)
    have hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯ := by
      have := sub_mem (add_mem hm hm) (one_mem _)
      convert this using 1
      ring
    exact absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)
  · have hm := mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])
    have hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯ := by simpa [sqrtNegNat] using hm
    have := Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')
    omega
  · exact (hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1,
      (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable : ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L → L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  atlas_forward_decl GlobalTheory.CMModel.integersLattice_invariants_ne_zero
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_ker_point_sqrtNegNat {p : ℕ} (hp : 1 < p) (L : PeriodPair)
    (hL : MulStable L (sqrtNegNat p)) :
    ∃ t : ℂ, t ∉ L.lattice ∧ sqrtNegNat p * t ∈ L.lattice := by
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    rw [sqrtNegNat, map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg p), mul_one]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have h0 : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    linarith
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hL
  have hc := kerRepsCard L _ S h0 hL hS
  rw [hn] at hc
  have hpos : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by
      push_cast at hc
      linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ := hpos
  have := hS.1 t ht
  exact ⟨t, by tauto, by tauto⟩

theorem g₂_mem_adjoin_j_of_eq (L : PeriodPair) (h0 : L.g₂ ≠ 0) (h : L.g₃ = L.g₂) :
    L.g₂ ∈ ℚ⟮(latticeCurve L).j⟯ := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ, h] at hΔ
  have h27 : L.g₂ - 27 ≠ 0 := fun e => hΔ (by linear_combination L.g₂ ^ 2 * e)
  have hj : (latticeCurve L).j = 1728 * L.g₂ / (L.g₂ - 27) := by
    rw [latticeCurve_j_eq, h, div_eq_div_iff hΔ h27]
    ring
  have hj' : (latticeCurve L).j - 1728 = 1728 * 27 / (L.g₂ - 27) := by
    rw [hj]
    field_simp
    ring
  have e : L.g₂ = 27 * (latticeCurve L).j / ((latticeCurve L).j - 1728) := by
    rw [hj', hj]
    field_simp
  have hm := IntermediateField.mem_adjoin_simple_self ℚ (latticeCurve L).j
  rw [e]
  exact div_mem (mul_mem (ofNat_mem _ 27) hm) (sub_mem hm (ofNat_mem _ 1728))

theorem exists_datum_of_isIntegersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 →
    3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ),
      Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  intro p L₀ hp _ h3 hL₀
  obtain ⟨h2, h3', hmul⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L₀.g₃ / L₀.g₂) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact div_ne_zero h3' h2 (by rw [← hc]; simp)
  obtain ⟨L, hlat, hg2, hg3, -, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L₀ c hc0
  have hmul' : MulStable L (sqrtNegNat p) := by
    intro ω hω
    have h1 : c⁻¹ * ω ∈ L₀.lattice := (hlat _).mp (by rwa [mul_inv_cancel_left₀ hc0])
    have h2 := (hlat _).mpr (hmul _ h1)
    rwa [mul_left_comm, mul_inv_cancel_left₀ hc0] at h2
  have hne : L.g₂ ≠ 0 := by
    rw [hg2]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc0)) h2
  have heq : L.g₃ = L.g₂ := by
    have : L₀.g₃ = c ^ 2 * L₀.g₂ := by rw [hc, div_mul_cancel₀ _ h2]
    rw [hg2, hg3, this]
    field_simp
  have hmem := g₂_mem_adjoin_j_of_eq L hne heq
  rw [hj] at hmem
  obtain ⟨t, ht, ht'⟩ := exists_ker_point_sqrtNegNat hp.one_lt L hmul'
  exact ⟨L, t, ⟨hmul', hmem, heq ▸ hmem, ht, ht'⟩, hj⟩

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 → 3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ), Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  atlas_forward_decl GlobalTheory.CMModel.exists_datum_of_isIntegersLattice
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_datum_sqProd_mem :
    ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p →
      Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧
        (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  intro p F L t hp h4 h3 hD
  set c := sqProd p L t with hc
  have hc0 : c ≠ 0 := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
  have hc2 : c ^ 2 ∈ F := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1
  obtain ⟨L', hlat, hg₂, hg₃, hder, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0
  obtain ⟨hcard, -⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4
  refine ⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩
  · intro ω hω
    have hz : c * (c⁻¹ * ω) ∈ L'.lattice := by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hz' := (hlat _).1 hz
    have := (hlat _).2 (hD.mul _ hz')
    rwa [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul] at this
  · rw [hg₂]
    have : (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem
  · rw [hg₃]
    have : (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem
  · rw [hlat]; exact hD.notMem
  · have := (hlat _).2 hD.ker
    rwa [← mul_assoc, mul_comm c, mul_assoc] at this
  · have hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c := by
      unfold sqProd
      have : ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) =
          (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k) := by
        intro k
        unfold sqPt
        rw [← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]
      rfl
    rw [hprod]
    set n := Fintype.card (Sq p) with hn
    have : ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹ := by
      obtain ⟨m, hm⟩ : Odd n := (GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2
      rw [hm]
      have : (2 * m + 1 - 1) / 2 = m := by omega
      rw [this]
      apply eq_inv_of_mul_eq_one_left
      rw [inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring,
        inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]
    rw [this]
    exact inv_mem (pow_mem hc2 _)

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧ (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  atlas_forward_decl GlobalTheory.CMModel.exists_datum_sqProd_mem
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_integral_of_modelAt (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F)
    (hV : ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) (hD : D ≠ 0)
    (h : ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ)) :
    ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ),
      (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧
        (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  obtain ⟨C, hu, hr, hs, ht, ⟨h1, h2, h3, h4, h6⟩, hΔ⟩ := h
  have hu0 : (⟨(C.u : ℂ), hu⟩ : F) ≠ 0 := by
    intro h0
    exact C.u.ne_zero (congrArg (fun x : F => (x : ℂ)) h0)
  let C' : VariableChange F := ⟨Units.mk0 _ hu0, ⟨C.r, hr⟩, ⟨C.s, hs⟩, ⟨C.t, ht⟩⟩
  have hC : C'.map (algebraMap F ℂ) = C := by
    ext <;> rfl
  have hmap : (C' • A).map (algebraMap F ℂ) = C • A.map (algebraMap F ℂ) := by
    rw [← hC, map_variableChange]
  rw [← hmap] at h1 h2 h3 h4 h6 hΔ
  set W := C' • A with hW
  have hD' : (D : ℂ) ≠ 0 := fun h0 => hD (Subtype.ext h0)
  have hvD : V.valuation (D : ℂ) ≠ 0 := by simpa using hD'
  rw [map_Δ] at hΔ
  have hΔ' : V.valuation ((W.Δ : F) : ℂ) = V.valuation (D : ℂ) := hΔ
  have hW0 : W.Δ ≠ 0 := by
    intro h0
    rw [h0] at hΔ'
    exact hvD (by simpa using hΔ'.symm)
  have hx : W.Δ / D ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  have hy : D / W.Δ ∈ w.valuationSubringAtPrime F := by
    rw [← hV, ← V.valuation_le_one_iff]
    push_cast
    rw [map_div₀, hΔ', div_self hvD]
  refine ⟨C', ⟨⟨_, hx⟩, ⟨_, hy⟩, ?_, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    show W.Δ / D * (D / W.Δ) = 1
    field_simp
  · apply Subtype.ext
    show D / W.Δ * (W.Δ / D) = 1
    field_simp
  · refine ⟨⟨⟨⟨W.a₁, (hV _).1 h1⟩, ⟨W.a₂, (hV _).1 h2⟩, ⟨W.a₃, (hV _).1 h3⟩, ⟨W.a₄, (hV _).1 h4⟩,
      ⟨W.a₆, (hV _).1 h6⟩⟩, ?_⟩⟩
    ext <;> rfl
  · show W.Δ = W.Δ / D * D
    field_simp

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F), (∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) → D ≠ 0 → ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ) → ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ), (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧ (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  atlas_forward_decl GlobalTheory.CMModel.exists_integral_of_modelAt
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)

end GlobalTheory.CMModel
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)), ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  atlas_forward_decl GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime
end

section
open IsDedekindDomain WeierstrassCurve

namespace GlobalTheory

theorem isMinimal_of_forall_div_pow_twelve (R F : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve F) (hI : W.IsIntegral R)
    (h : ∀ x : R, x ≠ 0 → W.Δ / algebraMap R F x ^ 12 ∈ (algebraMap R F).range → IsUnit x) :
    W.IsMinimal R := by
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have hC' : (C • W).IsIntegral R := hC
  rw [← Subtype.coe_le_coe]
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral]
  set v := HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hle : ∀ r : R, v (algebraMap R F r) ≤ 1 := fun r =>
    HeightOneSpectrum.valuation_le_one (K := F) (IsDiscreteValuationRing.maximalIdeal R) r
  rw [variableChange_Δ, map_mul, map_pow]
  refine mul_le_of_le_one_left' (pow_le_one' ?_ _)
  rcases ValuationRing.isInteger_or_isInteger R (C.u : F) with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact C.u.ne_zero (by simpa using hx.symm)
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R (C • W)
    have hu : IsUnit x := h x hx0 ⟨r, by
      rw [hr, variableChange_Δ, hx, Units.val_inv_eq_inv_val, inv_pow, div_eq_inv_mul]⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have : ((C.u⁻¹ : Fˣ) : F) = algebraMap R F y := by
      rw [Units.val_inv_eq_inv_val, ← hx]
      exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, hy, map_one])).symm
    rw [this]
    exact hle y
  · rw [Units.val_inv_eq_inv_val, ← hx]
    exact hle x

end GlobalTheory
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isMinimal_of_discr_eq_unit_mul_neg_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  intro p F _ _ w W u hp hI hΔ
  have hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1 := by
    intro y
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rfl
  refine GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_
  intro x hx0 hx
  by_contra hnu
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hx1 : w.valuation F (x : F) < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)
    have hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F := by
      rw [hmem, map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))
  have hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1 := by
    have h1 := (hmem _).1 (u : w.valuationSubringAtPrime F).2
    have h2 := (hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2
    have h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) *
        w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]; simp
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ _ * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  obtain ⟨y, hy⟩ := hx
  have hy1 := (hmem _).1 y.2
  have hyx : (y : F) * (x : F) ^ 12 = W.Δ := by
    have : (y : F) = W.Δ / (x : F) ^ 12 := hy
    rw [this]; field_simp
  have hv := congrArg (w.valuation F) (hyx.trans hΔ)
  rw [map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul] at hv
  have hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F) := by
    rw [← w.valuation_of_algebraMap (K := F)]; simp
  have hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F) := by
    rw [hpv]
    by_contra h
    exact hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))
  have hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12 := by
    rw [← hv]
    calc _ ≤ 1 * _ := mul_le_mul_left hy1 _
      _ = _ := one_mul _
  have hvx0 : w.valuation F (x : F) ≠ 0 := by simpa using hxF
  have hvp0 : w.valuation F (p : F) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  rw [← WithZero.exp_log hvx0] at hle hx1
  rw [← WithZero.exp_log hvp0] at hle hp'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hp'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx1
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  omega

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  atlas_forward_decl GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube
end

section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1

end GlobalTheory.CMModel
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' : ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  atlas_forward_decl GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom
end

section
open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  atlas_forward_decl GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem mem_prime_sq_of_sq_mem_prime_cube {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (Y : A) (h : Y ^ 2 ∈ P ^ 3) : Y ∈ P ^ 2 := by
  have hY : Y ∈ P := hP.mem_of_pow_mem 2 (Ideal.pow_le_self (by norm_num) h)
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : P ∣ Ideal.span {Y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hY)
  obtain ⟨J, hJ⟩ := hdvd
  have h2 : P ^ 3 ∣ Ideal.span {Y} ^ 2 := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
  rw [hJ, mul_pow, show P ^ 3 = P ^ 2 * P by ring] at h2
  have hP2 : P ^ 2 ≠ 0 := pow_ne_zero _ hP0
  have h3 : P ∣ J ^ 2 := (mul_dvd_mul_iff_left hP2).mp h2
  have h4 : P ∣ J := hprime.dvd_of_dvd_pow h3
  have h5 : P ^ 2 ∣ Ideal.span {Y} := by
    rw [hJ, sq]; exact mul_dvd_mul_left P h4
  exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd h5)

theorem natPrime_not_mem_cube_of_isUnramifiedAt :
    ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  intro p K H _ _ _ _ _ x P _ hp hK hx hP hunr hpP
  have hint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hx]
  set y : 𝓞 K := ⟨x, hint⟩ with hydef
  have hy : y ^ 2 = -(p : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast]
    exact hx
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0] at hy
    have : ((p : 𝓞 K)) = 0 := by simpa using hy.symm
    exact hp.ne_zero (by exact_mod_cast this)
  have hprime : (Ideal.span {y}).IsPrime := GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic p K y hp hK hy
  set Y : 𝓞 H := algebraMap (𝓞 K) (𝓞 H) y with hYdef
  have hpY : (p : 𝓞 H) = -(Y ^ 2) := by
    rw [hYdef, ← map_pow, hy, map_neg, map_natCast, neg_neg]
  have hY2 : Y ^ 2 ∈ P ^ 3 := by
    have := (P ^ 3).neg_mem_iff.mpr hpP
    rwa [hpY, neg_neg] at this
  have hYP2 : Y ∈ P ^ 2 := mem_prime_sq_of_sq_mem_prime_cube P hP Y hY2
  have hYP : Y ∈ P := Ideal.pow_le_self (by norm_num) hYP2
  have hyU : y ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap]; exact hYP
  have hU0 : P.under (𝓞 K) ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hyU; exact hy0 hyU
  have hspan : Ideal.span {y} = P.under (𝓞 K) := by
    have hmax : (Ideal.span {y}).IsMaximal :=
      hprime.isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hy0)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hyU)
  have he : P.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 K)) P hU0] at he
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) (P.under (𝓞 K)) ≤ P := Ideal.map_comap_le
  have hne := (Ideal.ramificationIdx'_ne_one_iff hle).not
  apply hne.mp (not_not.mpr he)
  rw [← hspan, Ideal.map_span, Set.image_singleton]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hYP2

end GlobalTheory
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt : ∀ (p : ℕ) (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] (x : K) (P : Ideal (𝓞 H)) [P.IsPrime], p.Prime → Module.finrank ℚ K = 2 → x ^ 2 = -(p : K) → P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P → (p : 𝓞 H) ∉ P ^ 3 := by
  atlas_forward_decl GlobalTheory.natPrime_not_mem_cube_of_isUnramifiedAt
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem natCast_notMem_pow_three_of_quadratic (p : ℕ) (K : Type) [Field K] [NumberField K]
    [Algebra K ℂ] (h2 : Module.finrank ℚ K = 2) (x : K) (hx : x ^ 2 = -(p : K))
    (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯]
    (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)) (hp : p.Prime)
    (hL : IsIntegersLattice p L₀) : (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro hw
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  obtain ⟨⟨⟨hfin, -, hun⟩, -⟩, -⟩ :=
    GlobalTheory.Laid.hcfj_holds K h2 L₀ ((isIntegersLattice_iff hp.pos h2 hx L₀).mp hL)
  have : NumberField K⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite K _
  have hle : ℚ⟮(latticeCurve L₀).j⟯ ≤
      (K⟮(latticeCurve L₀).j⟯.toSubfield.toIntermediateField fun q =>
        SubfieldClass.ratCast_mem _ q) :=
    IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self K _)
  let f : ℚ⟮(latticeCurve L₀).j⟯ →+* K⟮(latticeCurve L₀).j⟯ :=
    RingHom.codRestrict (algebraMap ℚ⟮(latticeCurve L₀).j⟯ ℂ) K⟮(latticeCurve L₀).j⟯
      fun z => hle z.2
  obtain ⟨P, hP, hP0, hPp⟩ := GlobalTheory.T.exists_prime_natCast_mem_pow_of_ringHom' _ _ f w p 3 hw
  exact GlobalTheory.T.natPrime_not_mem_prime_cube_of_isUnramifiedAt p K K⟮(latticeCurve L₀).j⟯ x P hp h2 hx hP0 (hun P hP0) hPp

theorem natCast_notMem_pow_three_adjoin_j : ∀ (p : ℕ) (L₀ : PeriodPair)
    [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)),
    p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  intro p L₀ _ w hp hL
  have hint : IsIntegral ℚ (sqrtNegNat p) :=
    IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)
  have : FiniteDimensional ℚ ℚ⟮sqrtNegNat p⟯ := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField ℚ⟮sqrtNegNat p⟯ := NumberField.of_module_finite ℚ _
  have hx : (IntermediateField.AdjoinSimple.gen ℚ (sqrtNegNat p)) ^ 2 =
      -(p : ℚ⟮sqrtNegNat p⟯) := Subtype.ext (by simpa using sqrtNegNat_sq p)
  have := isTotallyComplex_of_sq_eq_neg hp.pos hx
  have h2 : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ = 2 := by
    have hle : Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hm : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).Monic :=
        Polynomial.monic_X_pow_add_C _ two_ne_zero
      have := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ (sqrtNegNat p)
        (p := Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) (by simp [sqrtNegNat_sq])) hm.ne_zero
      rwa [Polynomial.natDegree_X_pow_add_C] at this
    have h1 := IsTotallyComplex.finrank ℚ⟮sqrtNegNat p⟯
    have h3 : 0 < Module.finrank ℚ ℚ⟮sqrtNegNat p⟯ := Module.finrank_pos
    omega
  exact natCast_notMem_pow_three_of_quadratic p _ h2 _ hx L₀ w hp hL

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  atlas_forward_decl GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem shortTwist_Δ (d a b : ℂ) :
    (shortTwist d a b).Δ = d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortTwist_c₄ (d a b : ℂ) :
    (shortTwist d a b).c₄ = d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [shortTwist, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortTwist_j {d a b : ℂ} (hd : d ≠ 0) [(shortTwist d a b).IsElliptic]
    [(⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).IsElliptic] :
    (shortTwist d a b).j = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).j := by
  have h0 : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ ≠ 0 :=
    (WeierstrassCurve.IsElliptic.isUnit (W := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ))).ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    shortTwist_Δ, shortTwist_c₄]
  field_simp

theorem j_congr_of_eq {W W' : WeierstrassCurve ℂ} (h : W = W') [W.IsElliptic] [W'.IsElliptic] :
    W.j = W'.j := by
  subst h; rfl

end GlobalTheory.CMModel

namespace GlobalTheory.Published

theorem cmCurveGoodOutsidePrime : CMCurveGoodOutsidePrimeSt := by
  intro p hp h4 h3
  obtain ⟨L₀, hL₀⟩ := exists_isIntegersLattice (p := p) hp.pos
  obtain ⟨-, -, hms⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  have him : (sqrtNegNat p).im ≠ 0 := by
    simp only [sqrtNegNat, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hjint := GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L₀ (sqrtNegNat p) hms him
  have hjQ : IsIntegral ℚ (latticeCurve L₀).j := hjint.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮(latticeCurve L₀).j⟯ := IntermediateField.adjoin.finiteDimensional hjQ
  haveI hNF : NumberField ℚ⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite ℚ _
  obtain ⟨L₁, t₁, hD₁, hj₁⟩ := GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice p L₀ hp h4 h3 hL₀
  obtain ⟨L, t, hD, hj, hsq⟩ := GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem p _ L₁ t₁ hp h4 h3 hD₁
  set F := ℚ⟮(latticeCurve L₀).j⟯ with hFdef
  have hg₂ : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) (ofNat_mem _ 4)
  have hg₃ : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) (ofNat_mem _ 4)
  let dF : F := if p % 8 = 3 then 1 else -(p : F)
  let dC : ℂ := if p % 8 = 3 then 1 else -(p : ℂ)
  have hdC : ((dF : F) : ℂ) = dC := by
    simp only [dF, dC]; split_ifs <;> simp
  have hdC0 : dC ≠ 0 := by
    simp only [dC]; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  let A : WeierstrassCurve F := shortTwist dF ⟨-L.g₂ / 4, hg₂⟩ ⟨-L.g₃ / 4, hg₃⟩
  have hmap : A.map (algebraMap F ℂ) = shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4) := by
    rw [← hdC]
    ext <;> simp [A, shortTwist, WeierstrassCurve.map]
  have hlat : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L := rfl
  have hΔA : A.Δ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap F ℂ) h0
    rw [← WeierstrassCurve.map_Δ, hmap, shortTwist_Δ, hlat, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hdC0) (latticeCurve_Δ_ne_zero L) this
  haveI hE : A.IsElliptic := ⟨Ne.isUnit hΔA⟩
  have hmin : HasMinimalDiscriminant A (-(p : F) ^ 3) := by
    intro w
    obtain ⟨V, hV⟩ := GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime F w
    have hloc := GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube p F L t hp h4 h3 hD hsq V
    have hD0 : (-(p : F) ^ 3) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    have hmod : ModelAt V F (A.map (algebraMap F ℂ)) ((-(p : F) ^ 3 : F) : ℂ) := by
      rw [hmap]
      convert hloc using 1
      push_cast; rfl
    obtain ⟨C, u, hI, hΔ⟩ := GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt F w V A _ hV hD0 hmod
    have hram := GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg p L₀ w hp hL₀
    exact ⟨C, u, GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube p F w (C • A) u hram hI hΔ, hΔ⟩
  refine ⟨F, hNF, A, ⟨hNF, hE, L₀, hL₀, rfl, ?_, hmin.hasGoodReductionOutside⟩, hmin⟩
  have e1 : ((A.j : F) : ℂ) = (A.map (algebraMap F ℂ)).j := (A.map_j (algebraMap F ℂ)).symm
  haveI : (shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4)).IsElliptic := hmap ▸ inferInstance
  haveI : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ).IsElliptic :=
    inferInstanceAs (latticeCurve L).IsElliptic
  rw [e1, j_congr_of_eq hmap, shortTwist_j hdC0, j_congr_of_eq hlat, hj, hj₁]

end GlobalTheory.Published
end
