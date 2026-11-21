import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFormalLogLiftCharacterSeries

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Limits

theorem smod_pow_iff {R : Type} [CommRing R] (a x y : R) (m : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ m • ⊤ : Submodule R R)] ↔ a ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eval_eq_of_le {O σ : Type} [CommRing O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hr : ∀ n f, r n (E (n + 1) f) = E n f) {n k : ℕ} (hnk : n ≤ k) (x y : MvPowerSeries σ O)
    (h : E k x = E k y) : E n x = E n y := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ih (by rw [← hr k x, ← hr k y, h])

theorem exists_unique_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] [Fintype σ] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)] [∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (y : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n), (∀ n, IsEval p (y n) (E n)) → (∀ n f, r n (E (n + 1) f) = E n f) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, (∀ n, E n f = 0) → f = 0) ∧ ((∀ n, Function.Surjective (E n)) → ∀ a : ∀ n, A n, (∀ n, r n (a (n + 1)) = a n) → ∃ f, ∀ n, E n f = a n) := by
  intro p O σ _ _ _ A _ _ _ r y E hev hr hker
  have hausO : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
  have precO : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
  have hle : ∀ {n k : ℕ}, n ≤ k → ∀ x y, E k x = E k y → E n x = E n y :=
    fun hnk => eval_eq_of_le A r E hr hnk
  refine ⟨fun f hf => ?_, fun hsurj a ha => ?_⟩
  · ext α
    refine hausO.haus _ fun m => (smod_pow_iff _ _ _ _).2 ?_
    obtain ⟨n, hn⟩ := hker m (α.degree + 1)
    simpa using hn f (hf n) α (Nat.lt_succ_self _)
  · choose nk hnk using fun m => hker m m
    choose g hg using fun n => hsurj n (a n)
    set ν : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nk j with hν
    have hνmono : Monotone ν := fun m m' hmm' => by
      simp only [hν]
      exact Nat.add_le_add hmm' (Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.succ_le_succ hmm')))
    have hνk : ∀ m, nk m ≤ ν m := fun m => by
      simp only [hν]
      exact le_add_left (Finset.single_le_sum (f := nk) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_self m)))
    have hνm : ∀ m, m ≤ ν m := fun m => by simp only [hν]; exact Nat.le_add_right _ _

    have hga : ∀ n k, n ≤ k → E n (g k) = a n := by
      intro n k hnk
      induction k, hnk using Nat.le_induction with
      | base => exact hg n
      | succ k hk ih =>
        rw [← ih]
        refine hle hk _ _ ?_
        rw [← hr k, hg (k + 1), ha k, hg k]

    have hKν : ∀ m k, ν m ≤ k → ∀ x, E k x = 0 → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α x := by
      intro m k hk x hx α hα
      refine hnk m x ?_ α hα
      have := hle ((hνk m).trans hk) x 0 (by rw [hx, map_zero])
      rwa [map_zero] at this
    set h : ℕ → MvPowerSeries σ O := fun m => g (ν m) with hh
    have hD : ∀ m m', m ≤ m' → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α (h m') - coeff α (h m) := by
      intro m m' hmm' α hα
      rw [← map_sub]
      refine hKν m (ν m) le_rfl _ ?_ α hα
      rw [map_sub, hh, hga _ _ (hνmono hmm'), hga _ _ le_rfl, sub_self]
    have hL : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ j, (p : O) ^ j ∣ coeff α (h (j + (α.degree + 1))) - L := by
      intro α
      obtain ⟨L, hL⟩ := precO.prec (f := fun j => coeff α (h (j + (α.degree + 1)))) (by
        intro j j' hjj'
        rw [smod_pow_iff]
        have := hD (j + (α.degree + 1)) (j' + (α.degree + 1)) (by omega) α (by omega)
        rw [← neg_sub, dvd_neg]
        exact (pow_dvd_pow _ (by omega)).trans this)
      exact ⟨L, fun j => (smod_pow_iff _ _ _ _).1 (hL j)⟩
    choose L hLs using hL
    let f : MvPowerSeries σ O := fun α => L α
    have hf : ∀ m M (α : σ →₀ ℕ), m ≤ M → α.degree < M →
        (p : O) ^ m ∣ coeff α f - coeff α (h M) := by
      intro m M α hmM hα
      have h1 := hLs α M
      have h2 := hD M (M + (α.degree + 1)) (by omega) α hα
      have : coeff α f - coeff α (h M) =
          (coeff α (h (M + (α.degree + 1))) - coeff α (h M)) -
            (coeff α (h (M + (α.degree + 1))) - L α) := by
        show L α - _ = _; ring
      rw [this]
      exact (pow_dvd_pow _ hmM).trans (dvd_sub h2 h1)
    refine ⟨f, fun n => ?_⟩
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(p : A n)}) inferInstance _ fun m => ?_
    rw [smod_pow_iff, sub_zero]
    obtain ⟨N₀, hN₀⟩ := (hev n).2 m
    set M := max (max m N₀) n with hM
    have hEM : E n (h M) = a n := hga _ _ ((le_max_right _ _).trans (hνm M))
    have hdiv : ∀ α : σ →₀ ℕ, α.degree < N₀ → (p : O) ^ m ∣ coeff α (f - h M) := by
      intro α hα
      rw [map_sub]
      exact hf m M α (by omega) (by omega)
    let Q : MvPowerSeries σ O := fun α =>
      if hα : α.degree < N₀ then Classical.choose (hdiv α hα) else 0
    have hR : ∀ α : σ →₀ ℕ, α.degree < N₀ →
        coeff α (f - h M - (p : O) ^ m • Q) = 0 := by
      intro α hα
      rw [map_sub, coeff_smul]
      show coeff α (f - h M) - (p : O) ^ m * (if hα : α.degree < N₀ then _ else 0) = 0
      rw [dif_pos hα, ← Classical.choose_spec (hdiv α hα), sub_self]
    have hsplit : E n f - a n = (p : A n) ^ m * E n Q + E n (f - h M - (p : O) ^ m • Q) := by
      rw [map_sub, map_sub, map_smul, hEM, Algebra.smul_def, map_pow, map_natCast]
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_right _ _) (hN₀ _ hR)

end GlobalTheory.Limits
end
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ}

theorem res_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    G.res n (c.ev (n + 1) f) = c.ev n f := by
  haveI : IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval (n + 1)) (G.res n : G.A (n + 1) →ₐ[O] G.A n)
  have h' : IsEval p (c.x n) ((G.res n : G.A (n + 1) →ₐ[O] G.A n).comp (c.ev (n + 1))) := by
    convert h using 2 with i
    exact (c.res n i).symm
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] G.A n => E f)
    (GlobalTheory.CEval.eval_unique p (c.x n) _ _ h' (c.isEval n))

theorem counit_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f := by
  let E₂ : MvPowerSeries (Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r) = r
        rw [← c_eq_algebraMap]; simp }
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval n) (Bialgebra.counitAlgHom O (G.A n))
  have h₁ : IsEval p (fun _ : Fin d => (0 : O))
      ((Bialgebra.counitAlgHom O (G.A n)).comp (c.ev n)) := by
    convert h using 2 with i
    exact (c.aug n i).symm
  have h₂ : IsEval p (fun _ : Fin d => (0 : O)) E₂ := by
    refine ⟨fun i => by simp [E₂], fun m => ⟨1, fun g hg => ?_⟩⟩
    have : constantCoeff g = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hg 0 (by simp)
    show (p : O) ^ m ∣ constantCoeff g
    rw [this]
    exact dvd_zero _
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] O => E f)
    (GlobalTheory.CEval.eval_unique p (fun _ => (0 : O)) _ _ h₁ h₂)

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog

theorem exists_charSeries : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  intro p _ O _ _ _ G d c χ
  haveI : ∀ n, IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) := fun n =>
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  obtain ⟨u, hu⟩ := (GlobalTheory.Limits.exists_unique_of_compatible p O (Fin d) G.A
    (fun n => (G.res n : G.A (n + 1) →ₐ[O] G.A n)) c.x c.ev c.isEval
    (fun n f => c.res_ev n f) c.ker).2 c.surj (charElem χ) (fun n => res_charElem χ n)
  refine ⟨u, ?_, hu⟩
  rw [← c.counit_ev 0 u, hu 0]
  exact (isGroupLikeElem_charElem χ 0).counit_eq_one

end GlobalTheory.QLog
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charSeries' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  atlas_forward_decl GlobalTheory.QLog.exists_charSeries
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) → subst c.μ u = inL u * inR u := by
  atlas_forward_decl GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FormalCalc

theorem lin_formalLog (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q) :
    constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  intro hg i
  have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (mul_pderiv_formalLog hg i)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hg, one_mul, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pderiv, coeff_pderiv] at h
  simpa [lin] using h

end GlobalTheory.FormalCalc
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  atlas_forward_decl GlobalTheory.FormalCalc.lin_formalLog
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.CobLog

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem hasSubst_inl : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst hasSubst_inl]
  simp

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst hasSubst_inr]
  simp

theorem constantCoeff_subst_one {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 1) :
    constantCoeff (subst a f) = 1 := by
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]

theorem constantCoeff_inL {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inL f) = 1 :=
  constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf

theorem constantCoeff_inR {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inR f) = 1 :=
  constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf

end SlopeTestRemainingChoices

theorem cob1_formalLog_mem_ker : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) →
    ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 →
    subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) →
    In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  intro p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul
  have hsμ : HasSubst μ' := hasSubst_of_constantCoeff_zero hμ
  have hμQ : ∀ i, constantCoeff (up Q μ' i) = 0 := fun i => by
    simp [up, hμ i]
  have hsμQ : HasSubst (up Q μ') := hasSubst_of_constantCoeff_zero hμQ
  set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def
  set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def
  have ha1 : constantCoeff a = 1 := constantCoeff_subst_one hsμ hμ hg
  have hbL : constantCoeff (inL g) = 1 := constantCoeff_inL hg
  have hbR : constantCoeff (inR g) = 1 := constantCoeff_inR hg
  have hb1 : constantCoeff b = ((1 : Bˣ) : B) := by simp [hb_def, hbL, hbR]
  set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def
  have hab : a = h * b := by
    rw [hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, map_mul, ha1, constantCoeff_invOfUnit]
    simp

  have hG : constantCoeff (map (algebraMap B Q) g) = 1 := by simp [hg]
  have key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) =
      formalLog (map (algebraMap B Q) h) := by
    unfold cob1
    have e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) =
        formalLog (map (algebraMap B Q) a) := by
      rw [subst_formalLog hsμQ hG, ha_def, map_subst hsμ]
      rfl
    have e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g)) := by
      rw [map_inL]
      exact subst_formalLog hasSubst_inl hG
    have e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g)) := by
      rw [map_inR]
      exact subst_formalLog hasSubst_inr hG
    have hmh : constantCoeff (map (algebraMap B Q) h) = 1 := by simp [hh1]
    have hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1 := by simp [hbL]
    have hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1 := by simp [hbR]
    have e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) +
        formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g)) := by
      rw [hab, hb_def, ← mul_assoc, map_mul, map_mul,
        formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]
    rw [e1, e2, e3, e4]
    abel

  have hθb : IsUnit (map θ b) := isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])
  have hθh : map θ h = 1 := by
    have h1 : map θ a = map θ b := by
      rw [ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]
    rw [hab, map_mul] at h1
    exact (IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)
  have hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
    exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
  have hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ := by
    intro α
    rw [RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]
  rw [key]
  exact GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker

end GlobalTheory.CobLog
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) → ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 → subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) → In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  atlas_forward_decl GlobalTheory.CobLog.cob1_formalLog_mem_ker
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FrobCong

theorem frobenius_congr (p : ℕ) [hpf : Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B)
    (hσ : ∀ b, (p : B) ∣ σB b - b ^ p) (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ) :
    (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  have hp : p ≠ 0 := hpf.out.ne_zero
  set I : Ideal B := Ideal.span {(p : B)} with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I with hπ
  have hsub : subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g)
      = expand p hp (map σB g) := by
    rw [expand, substAlgHom_apply]
  rw [hsub, ← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ,
    ← coeff_map, map_sub, map_pow, map_expand, map_map]
  rcases subsingleton_or_nontrivial (B ⧸ I) with hs | hs
  · exact Subsingleton.elim _ _
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    have h1 : π (p : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rwa [map_natCast] at h1
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hpf.out).2 hp0
  haveI : ExpChar (B ⧸ I) p := ExpChar.prime hpf.out
  have hcomp : π.comp σB = (frobenius (B ⧸ I) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [hcomp, ← map_map, ← map_expand, map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCong
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B), (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ), (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  atlas_forward_decl GlobalTheory.FrobCong.frobenius_congr
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_formalLog_sub_smul_integral : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) → (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 → In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) - (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  atlas_forward_decl GlobalTheory.QLog.in_frob_formalLog_sub_smul
end

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

open GlobalTheory.PDiv

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem exists_eq_add_single {α : Fin d →₀ ℕ} (h : α ≠ 0) :
    ∃ (i : Fin d) (β : Fin d →₀ ℕ), α = β + Finsupp.single i 1 ∧ α.degree = β.degree + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext hc)
  have hle : Finsupp.single i 1 ≤ α := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  refine ⟨i, α - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  conv_lhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

variable (c : Chart G d)

theorem counit_ev_monomial (n : ℕ) {β : Fin d →₀ ℕ} (hβ : β ≠ 0) (a : O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n (monomial β a)) = 0 := by
  obtain ⟨i, γ, rfl, -⟩ := exists_eq_add_single hβ
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, map_mul]
  change _ * Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, mul_zero]

theorem dUnit_ev_monomial (n : ℕ) {α : Fin d →₀ ℕ} (hα : 2 ≤ α.degree) (a : O) :
    dUnit O (c.ev n (monomial α a)) = 0 := by
  have h0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single h0
  have hβ : β ≠ 0 := by
    have hb : β.degree ≠ 0 := by omega
    exact fun h => hb (by rw [h]; simp)
  rw [← mul_one a, ← monomial_mul_monomial, map_mul, dUnit, AugCot.d_mul,
    c.counit_ev_monomial n hβ]
  change _ • _ + Bialgebra.counitAlgHom O (G.A n) (c.ev n (X i)) • _ = 0
  rw [(c.isEval n).1 i, Bialgebra.counitAlgHom_apply O (G.A n) (c.x n i), c.aug, zero_smul, zero_smul, add_zero]

theorem dUnit_ev_of_high (n N : ℕ) (hN : ∀ f : MvPowerSeries (Fin d) O,
    (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → (p : G.A n) ^ n ∣ c.ev n f)
    (f : MvPowerSeries (Fin d) O) (hf : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) :
    dUnit O (c.ev n f) = 0 := by
  obtain ⟨b, hb⟩ := hN f hf
  rw [hb, dUnit, AugCot.d_mul]
  have h1 : ((p : G.A n) ^ n) = algebraMap O (G.A n) ((p : O) ^ n) := by simp
  rw [h1, AugCot.d_algebraMap, smul_zero, add_zero, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply]
  exact G.pow_smul_cot n _

theorem dUnit_ev_of_two (n : ℕ) (f : MvPowerSeries (Fin d) O)
    (hf : ∀ α : Fin d →₀ ℕ, α.degree ≤ 1 → coeff α f = 0) : dUnit O (c.ev n f) = 0 := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  classical
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) f with hP
  have hsplit : f = (P : MvPowerSeries (Fin d) O) + (f - P) := by ring
  rw [hsplit, map_add, dUnit, map_add, ← dUnit, ← dUnit]
  rw [c.dUnit_ev_of_high n N hN (f - P) fun α hα => ?_, add_zero]
  · rw [MvPolynomial.as_sum P]
    have : ((∑ v ∈ P.support, MvPolynomial.monomial v (MvPolynomial.coeff v P) :
        MvPolynomial (Fin d) O) : MvPowerSeries (Fin d) O) =
        ∑ v ∈ P.support, monomial v (MvPolynomial.coeff v P) := by
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]
    rw [this, map_sum, dUnit, map_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv' : MvPolynomial.coeff v P ≠ 0 := MvPolynomial.mem_support_iff.1 hv
    have h2 : 2 ≤ v.degree := by
      by_contra hc
      apply hv'
      rw [hP, coeff_trunc']
      split_ifs
      · exact hf v (by omega)
      · rfl
    exact c.dUnit_ev_monomial n h2 _
  · rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro j
    exact ((Finsupp.le_degree j α).trans hα.le)

theorem dlog_eq_sum_lin [Fact p.Prime] (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O)
    (h1 : constantCoeff u = 1) (hu : ∀ n, c.ev n u = charElem χ n) :
    dlog G χ = ∑ i, lin u i • c.form i := by
  classical
  apply Subtype.ext
  funext n
  rw [Submodule.coe_sum, Finset.sum_apply, dlog_val, ← hu n]
  simp only [Submodule.coe_smul, Pi.smul_apply]
  set g : MvPowerSeries (Fin d) O := ∑ i, lin u i • X i with hg
  have hsplit : u = 1 + g + (u - 1 - g) := by ring
  have hev : c.ev n g = ∑ i, lin u i • c.x n i := by
    rw [hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, (c.isEval n).1 i]
  have e1 : dUnit O (c.ev n u) = dUnit O (c.ev n 1) + dUnit O (c.ev n g) +
      dUnit O (c.ev n (u - 1 - g)) := by
    conv_lhs => rw [hsplit]
    simp only [PDiv.dUnit, map_add]
  rw [e1, c.dUnit_ev_of_two n (u - 1 - g) ?_, add_zero, map_one, hev]
  · simp only [PDiv.dUnit, AugCot.d_one, zero_add, map_sum, map_smul]
    rfl
  intro α hα
  have hcg : ∀ i, coeff (Finsupp.single i 1) g = lin u i := fun i => by
    rw [hg, map_sum]
    simp only [map_smul, coeff_X, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1'
  · rw [(Finsupp.degree_eq_zero_iff α).1 h0]
    have hg0 : coeff 0 g = 0 := by
      rw [hg, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_X, if_neg, smul_zero]
      intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this
    rw [map_sub, map_sub, hg0, coeff_zero_eq_constantCoeff_apply, h1,
      coeff_zero_eq_constantCoeff_apply, map_one]
    ring
  · have hne : α ≠ 0 := by
      rintro rfl
      simp at h1'
    obtain ⟨i, β, rfl, hdeg⟩ := exists_eq_add_single hne
    have hβ : β = 0 := (Finsupp.degree_eq_zero_iff β).1 (by omega)
    subst hβ
    rw [zero_add, map_sub, map_sub, hcg, coeff_one, if_neg, sub_zero]
    · exact sub_self _
    · intro h
      have := congrArg (fun a : Fin d →₀ ℕ => a i) h
      simp at this

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem dlog_eq_sum_lin' : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i :=
  fun _ _ _ _ _ _ _ _ c χ u h1 hu => c.dlog_eq_sum_lin χ u h1 hu

end GlobalTheory.QLog.Chart
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i := by
  atlas_forward_decl GlobalTheory.QLog.Chart.dlog_eq_sum_lin'
end

section
section
namespace GlobalTheory.CharLog

variable {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O}

theorem isUnit_intCast [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) {n : ℤ} (hn : n ≠ 0) :
    IsUnit (n : Q) := by
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hna p (Fact.out : p.Prime).ne_one
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
  have hu : IsUnit (n.natAbs : Q) := by
    rw [hnm, Nat.cast_mul, Nat.cast_pow]
    refine (h.unit_p.pow k).mul ?_
    simpa using (h.unit_coprime m hcop).map (algebraMap B Q)
  rcases Int.natAbs_eq n with h' | h'
  · rw [h', Int.cast_natCast]; exact hu
  · rw [h', Int.cast_neg, Int.cast_natCast]; exact hu.neg

noncomputable def ratAlgebra [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) : Algebra ℚ Q :=
  (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom Q)
    fun y => by simpa using isUnit_intCast h (nonZeroDivisors.ne_zero y.2)).toAlgebra

end GlobalTheory.CharLog

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem GlobalTheory.CharLog.exists_log_char_period : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ χ
  letI : Algebra ℚ F.Q := GlobalTheory.CharLog.ratAlgebra F.frame
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_charSeries' p O G d c χ
  have hmul := GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter p O G d c χ u hu
  choose g0 hg0 using fun α => F.frame.surj (coeff α u)
  let g : MvPowerSeries (Fin d) F.B := fun α => if α = 0 then 1 else g0 α
  have hg : map F.θ g = u := by
    ext α
    rw [coeff_map]
    by_cases h : α = 0
    · subst h
      change F.θ (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = _
      rw [if_pos rfl, map_one, coeff_zero_eq_constantCoeff_apply, hu0]
    · change F.θ (if α = 0 then 1 else g0 α) = _
      rw [if_neg h, hg0]
  have hg1 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    change (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = 1
    rw [if_pos rfl]
  have hlin : ∀ i, lin (formalLog (map (algebraMap F.B F.Q) g)) i =
      algebraMap F.B F.Q (coeff (Finsupp.single i 1) g) := fun i => by
    rw [GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog F.Q d _ (by rw [constantCoeff_map, hg1, map_one]) i, lin, coeff_map]
  have hcob := GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike p F.B O F.Q F.θ F.frame d μ' hlift.const g hg1 (by
    rw [hg]; convert hmul using 2; funext i; exact hμ i)
  refine ⟨formalLog (map (algebraMap F.B F.Q) g), fun i => coeff (Finsupp.single i 1) g,
    ⟨constantCoeff_formalLog (by rw [constantCoeff_map, hg1, map_one]),
      fun i => ⟨_, Submodule.mem_top, hlin i⟩,
      fun α => by obtain ⟨b, -, hb⟩ := hcob α; exact ⟨b, Submodule.mem_top, hb⟩⟩,
    hcob, GlobalTheory.T.frobenius_formalLog_sub_smul_integral p F.B O F.Q F.θ F.frame F.σ F.s F.s_alg F.σ_pow d g hg1, hlin, ?_, ?_⟩
  · rw [GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit p O G d c χ u hu0 hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg, lin, coeff_map]
  · exact GlobalTheory.T.period_formalLog_lift_characterSeries p C v O hv ε hε F G d c χ g hg1 (by rw [hg]; exact hu)
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiLogarithm_of_dualCharacter : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  atlas_forward_decl GlobalTheory.CharLog.exists_log_char_period
end
