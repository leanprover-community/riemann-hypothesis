import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowRescale
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.NormalModularTowerTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.AlgEquivMemRingOfIntegersModularTowerTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.MemRingOfIntegersModularTowerTopOfForallValuatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.ExistsIsLocallyConstantLiftToGeometricGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.ValuationSiegelUnitLevelEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.AdmissibleUnits

open GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem ent_ext {g h : GQ} (e : ∀ i j, ent g i j = ent h i j) : g = h :=
  Subtype.ext (Matrix.GeneralLinearGroup.ext e)

private theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ent_dg {N : ℕ} (hN : 0 < N) (i j : Fin 2) :
    ent (toGQ !![(N : ℤ), 0; 0, 1]) i j = (!![(N : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  fin_cases i <;> fin_cases j <;> simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem ent_sl (γ : SL(2, ℤ)) (i j : Fin 2) : ent (ofSL γ) i j = (en γ i j : ℚ) := rfl

private theorem dg_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    toGQ !![(a : ℤ), 0; 0, 1] * toGQ !![(b : ℤ), 0; 0, 1] = toGQ !![((a * b : ℕ) : ℤ), 0; 0, 1] := by
  refine ent_ext fun i j => ?_
  rw [ent_mul, ent_dg (Nat.mul_pos ha hb)]
  simp only [ent_dg ha, ent_dg hb]
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) :
    ∃ δ : SL(2, ℤ), en δ 0 0 = en γ 0 0 ∧ en δ 0 1 = N * en γ 0 1 ∧ en δ 1 0 = k ∧ en δ 1 1 = en γ 1 1 ∧
      toGQ !![(N : ℤ), 0; 0, 1] * ofSL γ = ofSL δ * toGQ !![(N : ℤ), 0; 0, 1] := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  let δ : SL(2, ℤ) := ⟨!![en γ 0 0, N * en γ 0 1; k, en γ 1 1], by
    rw [Matrix.det_fin_two_of, ← hd, hk]; ring⟩
  have h00 : en δ 0 0 = en γ 0 0 := rfl
  have h01 : en δ 0 1 = N * en γ 0 1 := rfl
  have h10 : en δ 1 0 = k := rfl
  have h11 : en δ 1 1 = en γ 1 1 := rfl
  refine ⟨δ, h00, h01, h10, h11, ent_ext fun i j => ?_⟩
  rw [ent_mul, ent_mul]
  simp only [ent_dg hN, ent_sl]
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk, mul_comm]

private theorem admissible_of_integral_conj_le {c D : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcD : Nat.Coprime c D) (hD : 0 < D) {a b : ℤ}
    (hab : ¬ ((D : ℤ) ∣ a ∧ (D : ℤ) ∣ b)) : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D] := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : IsCoprime (D : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.2 hcD.symm
  have key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / D) ∈ Set.range ((↑) : ℤ → ℚ) → (D : ℤ) ∣ z := by
    rintro z ⟨k, hk⟩
    have e : (c : ℚ) * z = D * k := by rw [hk]; field_simp
    exact hz.dvd_of_dvd_mul_left ⟨k, by exact_mod_cast e⟩
  exact ⟨hc, h6, fun h => hab ⟨key a h.1, key b h.2⟩⟩

private theorem siegel_per {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : siegel X c y = siegel X c x := by
  have hy : y = fun i => x i + ((![p, q] : Fin 2 → ℤ) i : ℚ) := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have e : sgC c y = sgC c x := by
    funext z
    rw [hy]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ _ hx
  unfold siegel
  rw [e]

private theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : GlobalTheory.Sieg.admitted c y := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => hx.2.2 ⟨⟨u - c * p, ?_⟩, ⟨v - c * q, ?_⟩⟩⟩
  · push_cast; rw [hu, h0]; ring
  · push_cast; rw [hv, h1]; ring

private theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hq : (en γ 0 0 : ℚ) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by exact_mod_cast hd
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ =>
    hx.2.2 ⟨⟨u * en γ 1 1 - v * en γ 1 0, ?_⟩, ⟨v * en γ 0 0 - u * en γ 0 1, ?_⟩⟩⟩
  all_goals
    simp only [act, Fin.sum_univ_two] at hu hv
    simp only [en] at hq ⊢
    push_cast
    rw [hu, hv]
  · linear_combination (c * x 0) * hq
  · linear_combination (c * x 1) * hq

private theorem sl_dg_siegel [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N : ℕ} (hN : 0 < N) {x y : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) (p q : ℤ)
    (h0 : y 0 = x 0 * en γ 0 0 + x 1 * k + p) (h1 : y 1 = x 0 * (N * en γ 0 1) + x 1 * en γ 1 1 + q) :
    X.sl (ofSL γ) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c x)) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c y) := by
  obtain ⟨δ, h00, h01, h10, h11, e⟩ := exists_conj hN γ k hk
  rw [← X.sl_mul, e, X.sl_mul, GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c x δ hx]
  congr 1
  simp only [en] at h00 h01 h10 h11 h0 h1
  refine (siegel_per X (admissible_act_SL2 hx δ) p q ?_ ?_).symm
  · simp only [act, Fin.sum_univ_two]; rw [h0, h00, h10]
  · simp only [act, Fin.sum_univ_two]; rw [h1, h01, h11]; push_cast; ring

private theorem gal_siegel_fix [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c D : ℕ} (hD : 0 < D) {a b : ℤ}
    (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ z : Ω, z ^ D = 1 → s z = z) :
    X.gal s (siegel X c ![(a : ℚ) / D, (b : ℚ) / D]) = siegel X c ![(a : ℚ) / D, (b : ℚ) / D] := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hz)
  obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hz)
  have hlt : a' < D := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hD : (0 : ℤ) < D)
    omega
  have ea : (a : ℚ) = a' + D * ((a / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv a D
    rw [ha'] at this
    exact_mod_cast this.symm
  have eb : (b : ℚ) = b' + D * ((b / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv b D
    rw [hb'] at this
    exact_mod_cast this.symm
  have f0 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 0 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 0 + ((-(a / D) : ℤ) : ℚ) := by
    show (a' : ℚ) / D = (a : ℚ) / D + ((-(a / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -ea
  have f1 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 1 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 1 + ((-(b / D) : ℤ) : ℚ) := by
    show (b' : ℚ) / D = (b : ℚ) / D + ((-(b / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -eb
  have hy := isAdmissibleSmoothingFactor_add_intVector hx _ _ f0 f1
  rw [← siegel_per X hx _ _ f0 f1]
  have := GlobalTheory.T.galois_action_siegelUnitInTower Ω ε X c D a' b' 1 s hD hlt
    (by rw [Nat.cast_one]; exact hs _ (isPrimitiveRoot_eOm ε hD.ne').pow_eq_one) hy (by rwa [one_mul])
  rwa [one_mul] at this

private theorem gal_dg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) {f : X.K} (hf : X.gal s f = f) :
    X.gal s (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f := by
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, GlobalTheory.DlRescale.exp_sl_diag ε X N hN, GlobalTheory.DlRescale.resc_coeff, ← X.gal_exp, hf]

private theorem sgN_mem [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N D M : ℕ} (hN : 0 < N) (hD : 0 < D)
    (hM : N * D ∣ M) {a b : ℤ} (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) :
    sgN X c N D (a, b) ∈ topF X M ∧ sgN X c N D (a, b) ≠ 0 := by
  refine ⟨(mem_mdl_iff X _ _ _).2 ⟨?_, fun s hs => ?_⟩, ?_⟩
  · rw [mem_lev_iff]
    intro γ hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have hMz : ((N * D : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 hM
    obtain ⟨u, hu⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 0 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h00))
    obtain ⟨v, hv⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 1 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h01)
    obtain ⟨w, hw⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 0 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h10)
    obtain ⟨t, ht⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 1 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h11))
    have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    refine sl_dg_siegel X hN hx γ (D * w) (by rw [hw]; push_cast; ring) (-(a * N * u + b * w)) (-(a * N * N * v + b * N * t)) ?_ ?_
    · show (a : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 hu]; push_cast; field_simp; ring
    · show (b : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 ht, hv]; push_cast; field_simp; ring
  · refine gal_dg X hN s (gal_siegel_fix X hD hx s fun z hz => (mem_fixMu_iff s).1 hs z ?_)
    obtain ⟨e, rfl⟩ := (Dvd.intro_left N rfl : D ∣ N * D).trans hM
    rw [pow_mul, hz, one_pow]
  · exact (map_ne_zero _).2 (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c _ hx)

end UpperTheory.Kd.L.AdmissibleUnits

open UpperTheory.Kd.L.AdmissibleUnits in
theorem UpperTheory.Kd.L.units :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ((sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ∈ topF X (topMu l n m N) ∧ (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ≠ 0 ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ∈ topF X (topMu l n m N) ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ≠ 0) ∧ ∀ g ∈ CongruenceSubgroup.Gamma0 N, X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) = sgN X c (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n))), (N : ℤ) ^ 2 * ((N : ℤ) ^ 2 * en g 0 1)) ∧ X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) = sgN X d (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) + en g 1 0), (N : ℤ) ^ 2 * ((N : ℤ) * en g 1 1)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm P x m n hm
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hL : 0 < l ^ (m + n) := pow_pos hl _
  have hD : 0 < N * l ^ (m + n) := Nat.mul_pos hN hL
  have hlL : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
  have cop : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨he.coprime_mul_right_right.coprime_mul_right_right,
      Nat.Coprime.mul_right he.coprime_mul_left_right
        (Nat.Coprime.pow_right _ he.coprime_mul_right_right.coprime_mul_left_right)⟩
  have hlD : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (hlL.mul_left N)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => P.cop (Int.natCast_dvd_natCast.1 h)
  have hM : N * (N * l ^ (m + n)) ∣ topMu l n m N := ⟨1, by unfold topMu; ring⟩
  generalize (topT l (m + n) N : ℤ) = t
  have hu := admissible_of_integral_conj_le P.c1 (cop c P.cc).1 (cop c P.cc).2 hD
    (a := (N : ℤ) + (x.val : ℤ) * t * (l : ℤ) ^ (m + n)) (b := 0) (fun h => hlN
      ((dvd_add_left ((dvd_pow_self (l : ℤ) (by omega)).mul_left _)).1 (hlD.trans h.1)))
  have hv := admissible_of_integral_conj_le P.d1 (cop d P.dc).1 (cop d P.dc).2 hD
    (a := t * (l : ℤ) ^ (m + n)) (b := (N : ℤ)) (fun h => by
      have h2 := Nat.le_of_dvd hN (Int.natCast_dvd_natCast.1 h.2)
      have h3 : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
      nlinarith)
  refine ⟨⟨(sgN_mem X hN hD hM hu).1, (sgN_mem X hN hD hM hu).2, (sgN_mem X hN hD hM hv).1, (sgN_mem X hN hD hM hv).2⟩,
    fun g hg => ?_⟩
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ en g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hg)
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have e3 : N * (N * N) = N ^ 3 := by ring
  unfold sgN
  constructor
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hu g k hk 0 (-(x.val * t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hv g k hk 0 (-(t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hk]; push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
end

section
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
attribute [local instance] algMdl algPoly algRat

namespace UpperTheory.Kd.L.KummerExtensionIntegrality

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem resGeo {F K Kb : Type} [Field F] [Field K] [Field Kb] [Algebra F K] [Algebra F Kb] [Algebra K Kb] [IsScalarTower F K Kb]
    (g : Kb ≃ₐ[F] Kb) (hg : g ∈ geo F K Kb) : ∃ g' : Kb ≃ₐ[K] Kb, ∀ z, g' z = g z :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun a => (TopW.mem_geo g).1 hg a, fun _ => rfl⟩

private theorem kumRes {F K Kb : Type} [Field F] [Field K] [Field Kb] [Algebra F Kb] [Algebra K Kb] {N : ℕ} (ζ θ : Kb)
    {g : Kb ≃ₐ[F] Kb} {g' : Kb ≃ₐ[K] Kb} (h : ∀ z, g' z = g z) : kum (K := K) (N := N) ζ θ g' = kum (K := F) (N := N) ζ θ g := by
  have e := h θ
  unfold kum
  generalize g' θ = a at e ⊢
  subst e
  rfl

private theorem constInt (X : Tower Ω ε) (M : ℕ) (f : topL X M) (h : (f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) :
    f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  have key : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
    rcases h with h | ⟨c, h⟩
    · refine ⟨Polynomial.X, Subtype.ext ?_⟩
      show ((jPoly X _ Polynomial.X : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_X, h]
    · refine ⟨Polynomial.C c, Subtype.ext ?_⟩
      show ((jPoly X _ (Polynomial.C c) : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_C, h]
  obtain ⟨P, rfl⟩ := key
  exact isIntegral_algebraMap

private theorem polyMem (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M))
    (hB : ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) → algebraMap (topL X M) (topBar X M) f ∈ B)
    (P : Polynomial Ω) : algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) P) ∈ B := by
  have hC : ∀ c : Ω, algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) (Polynomial.C c)) ∈ B := fun c =>
    hB _ (Or.inr ⟨c, by
      show _ = ((jPoly X _ (Polynomial.C c) : topL X M) : X.K)
      rw [coe_jPoly, Polynomial.aeval_C]⟩)
  have hX : algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) Polynomial.X) ∈ B :=
    hB _ (Or.inl (by
      show ((jPoly X _ Polynomial.X : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_X]))
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul]
    exact mul_mem h hX

private theorem memOfInt (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M))
    (hB : ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) → algebraMap (topL X M) (topBar X M) f ∈ B)
    (x : topL X M) (hx : x ∈ FunctionField.ringOfIntegers Ω (topL X M)) : algebraMap (topL X M) (topBar X M) x ∈ B := by
  obtain ⟨p, hp, hev⟩ : IsIntegral (Polynomial Ω) x := hx
  let φ : Polynomial Ω →+* B :=
    ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))).codRestrict B.toSubring
      (fun P => polyMem X M B hB P)
  have hφ : (algebraMap B (topBar X M)).comp φ = (algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M)) := rfl
  have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) x) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ, ← Polynomial.hom_eval₂, hev, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

private theorem topexOf [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hd : l ^ n ∣ M) {u v : X.K}
    (hu : u ∈ topF X M) (hv : v ∈ topF X M) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hW : ∀ W : ValuationSubring X.K, X.OverY W → W.valuation u = 1 ∧ W.valuation v = 1) :
    IsTopEta X M (topChar X M l n u) (topChar X M l n v) (topEta X M (topChar X M l n u) (topChar X M l n v)) ∧
      ∀ σ : topGal X M, ∃ w : topL X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) σ w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl⟩
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI : Normal (topF X M) (topL X M) := UpperTheory.normal_modularTowerTop X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans (topF X M) (topL X M) (topBar X M)
  have hN : 0 < l ^ n := pow_pos (Nat.pos_of_ne_zero hl) n
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hfix := topGal_topZeta X hl hd
  let a : topL X M := ⟨u, mdl_le_lev X _ _ hu⟩
  let b : topL X M := ⟨v, mdl_le_lev X _ _ hv⟩
  let aF : topF X M := ⟨u, hu⟩
  let bF : topF X M := ⟨v, hv⟩
  have ha0 : a ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hb0 : b ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have haF0 : aF ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hbF0 : bF ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hpl : ∀ W : ValuationSubring X.K, X.OverY W → ∀ z : X.K, W.valuation z = 1 → z ∈ W ∧ z⁻¹ ∈ W := fun W _ z hz =>
    ⟨(W.valuation_le_one_iff z).1 hz.le, (W.valuation_le_one_iff _).1 (by rw [map_inv₀, hz, inv_one])⟩
  have hai : a ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M a fun W hw => (hpl W hw u (hW W hw).1).1
  have hbi : b ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M b fun W hw => (hpl W hw v (hW W hw).2).1
  have hai' : a⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M a⁻¹ fun W hw => (hpl W hw u (hW W hw).1).2
  have hbi' : b⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M b⁻¹ fun W hw => (hpl W hw v (hW W hw).2).2
  have hα : topRoot X M (l ^ n) u ^ (l ^ n) = algebraMap (topL X M) (topBar X M) a := topRoot_pow X M hN.ne' _
  have hβ : topRoot X M (l ^ n) v ^ (l ^ n) = algebraMap (topL X M) (topBar X M) b := topRoot_pow X M hN.ne' _
  have hαF : topRoot X M (l ^ n) u ^ (l ^ n) = algebraMap (topF X M) (topBar X M) aF := by
    rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]; rfl
  have hβF : topRoot X M (l ^ n) v ^ (l ^ n) = algebraMap (topF X M) (topBar X M) bF := by
    rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]; rfl
  have hx := topChar_apply X hl hd hu hu0
  have hy := topChar_apply X hl hd hv hv0
  obtain ⟨-, -, -, -, η₀, hlc, hcob, hin⟩ := GlobalTheory.T.kummerCupProduct_coboundary_theorem Ω (topL X M) (topBar X M) (l ^ n) (topZeta X M l n) hN hζ a b _ _ ha0 hb0
    hai hai' hbi hbi' hα hβ
  obtain ⟨η, hηlc, hηe⟩ := UpperTheory.exists_isLocallyConstant_lift_to_geometric_galois (F := topF X M) η₀ hlc
  have hex : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    refine ⟨η, ?_, hηlc, ?_⟩
    · intro g hg h hh
      obtain ⟨g', hg'⟩ := resGeo g hg
      obtain ⟨h', hh'⟩ := resGeo h hh
      have e1 := hηe g g' hg hg'
      have e2 := hηe h h' hh hh'
      have e3 := hηe (g * h) (g' * h') (mul_mem hg hh) fun z => by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg', hh']
      rw [e1, e2, e3, hx, hy, ← kumRes _ _ hg', ← kumRes _ _ hh']
      exact hcob g' h'
    · intro B g hB hI hg
      obtain ⟨g', hg'⟩ := resGeo g hg
      rw [hηe g g' hg hg']
      refine hin B (fun x hx => memOfInt X M B hB x hx) g' fun z hz => ?_
      rw [hg']
      exact hI z hz
  have hT := isTopEta_topEta X M hex
  refine ⟨hT, fun σ => ⟨topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) σ, ?_⟩⟩
  exact GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field Ω (topL X M) (topBar X M) (topF X M) (l ^ n) (topZeta X M l n) hN hζ hfix (UpperTheory.algEquiv_mem_ringOfIntegers_modularTowerTop X M) aF bF _ _ haF0 hbF0
    hai hai' hbi hbi' hαF hβF _ _ hx hy _ hT.1 hT.2.1
    (fun B g hB hI hg => hT.2.2 B g (fun f hf => hB _ (constInt X M f hf)) hI hg) σ

end UpperTheory.Kd.L.KummerExtensionIntegrality

theorem UpperTheory.Kd.L.topex :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → IsTopEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) (topEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))) ∧ ∀ σ : topGal X (topMu l n m N), ∃ w : topL X (topMu l n m N), IsTopW (K := topL X (topMu l n m N)) (topZeta X (topMu l n m N) l n) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) (topEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))) σ w := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP x m n hm
  have hl : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hD0 : 0 < N * l ^ (m + n) := Nat.mul_pos hN0 (pow_pos hl.pos _)
  obtain ⟨⟨hu, hu0, hv, hv0⟩, -⟩ := UpperTheory.Kd.L.units ε X l N c d gm hP x m n hm
  have hld : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := by
    exact_mod_cast Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N
  have hlp : (l : ℤ) ∣ (l : ℤ) ^ (m + n) := dvd_pow_self _ (by omega)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have c6 : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨Nat.Coprime.coprime_dvd_right (Dvd.intro _ (by rw [mul_assoc])) he,
      Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) he)
        (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (Dvd.dvd.mul_right (Dvd.intro_left 6 rfl) N) he))⟩
  refine KummerExtensionIntegrality.topexOf X (NeZero.ne _) hl.ne_zero ?_ hu hv hu0 hv0 fun W hW => ⟨?_, ?_⟩
  · exact Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _
  · refine UpperTheory.valuation_siegelUnitLevel_eq_one ε X c N _ _ hP.c1 (c6 c hP.cc).1 (c6 c hP.cc).2 hN0 hD0 (fun h => hlN ?_) W hW
    have h1 := hld.trans h.1
    have h2 : (l : ℤ) ∣ (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) := Dvd.dvd.mul_left hlp _
    exact (Int.dvd_add_left h2).1 h1
  · refine UpperTheory.valuation_siegelUnitLevel_eq_one ε X d N _ _ hP.d1 (c6 d hP.dc).1 (c6 d hP.dc).2 hN0 hD0 (fun h => hlN (hld.trans h.2)) W hW
end
