import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers

section
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartForm

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_coe (n : ℕ) (P : MvPolynomial (Fin d) O) :
    c.ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x n) P := by
  have h : (c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      MvPolynomial.aeval (c.x n) :=
    MvPolynomial.algHom_ext fun i => by
      simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (c.isEval n).1 i]
  have h2 := DFunLike.congr_fun h P
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using h2

theorem exists_split (n m : ℕ) (f : MvPowerSeries (Fin d) O) :
    ∃ (P : MvPolynomial (Fin d) O) (a : G.A n),
      c.ev n f = MvPolynomial.aeval (c.x n) P + (p : G.A n) ^ m * a ∧
      MvPolynomial.constantCoeff P = constantCoeff f ∧
      ∀ i, MvPolynomial.coeff (Finsupp.single i 1) P = lin f i := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 m
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => max N 2) f with hP
  have hle : ∀ α : Fin d →₀ ℕ, α.degree < max N 2 →
      α ≤ Finsupp.equivFunOnFinite.symm fun _ => max N 2 := by
    intro α hα i
    show α i ≤ max N 2
    exact (Finsupp.le_degree i α).trans hα.le
  obtain ⟨a, ha⟩ := hN (f - P) fun α hα => by
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc',
      if_pos (hle α (lt_of_lt_of_le hα (le_max_left _ _))), sub_self]
  refine ⟨P, a, ?_, ?_, fun i => ?_⟩
  · rw [← ev_coe, ← ha, ← map_add, add_sub_cancel]
  · rw [MvPolynomial.constantCoeff_eq, hP, coeff_trunc',
      if_pos (hle 0 (by simp)), coeff_zero_eq_constantCoeff_apply]
  · rw [hP, coeff_trunc', if_pos (hle _ (lt_of_lt_of_le (by simp) (le_max_right N 2))), lin]

theorem eq_zero_of_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ m, (p : O) ^ m ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun m => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h m

theorem counit_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (MvPolynomial.aeval (c.x n) P) =
      MvPolynomial.constantCoeff P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h : (fun i => Bialgebra.counitAlgHom O (G.A n) (c.x n i)) = 0 :=
    funext fun i => by simpa using c.aug n i
  rw [h, MvPolynomial.aeval_zero]
  rfl

theorem counit_ev [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ)
    (f : MvPowerSeries (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n f) = constantCoeff f := by
  refine sub_eq_zero.1 (eq_zero_of_dvd (p := p) _ fun m => ?_)
  obtain ⟨P, a, h1, h2, -⟩ := (exists_split c) n m f
  rw [h1, map_add, counit_aeval, h2, map_mul, map_pow, map_natCast, add_sub_cancel_left]
  exact dvd_mul_right _ _

theorem d_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    PDiv.dUnit O (MvPolynomial.aeval (c.x n) P) =
      ∑ i, MvPolynomial.coeff (Finsupp.single i 1) P • PDiv.dUnit O (c.x n i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : ∀ x : Fin d, ¬ (0 : Fin d →₀ ℕ) = Finsupp.single x 1 := fun x h =>
      (Finsupp.single_ne_zero.2 one_ne_zero) h.symm
    rw [MvPolynomial.aeval_C]
    simp [MvPolynomial.coeff_C, PDiv.dUnit, h0]
  | add P Q hP hQ =>
    unfold PDiv.dUnit at *
    rw [map_add, map_add, hP, hQ, ← Finset.sum_add_distrib]
    simp [add_smul]
  | mul_X P j h =>
    have hc : ∀ i, MvPolynomial.coeff (Finsupp.single i 1) (P * MvPolynomial.X j) =
        if j = i then MvPolynomial.constantCoeff P else 0 := by
      intro i
      rw [MvPolynomial.coeff_mul_X']
      by_cases hij : j = i
      · subst hij; simp [MvPolynomial.constantCoeff_eq]
      · simp [hij, Finsupp.support_single_ne_zero]
    simp only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx : Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := by simpa using c.aug n j
    rw [map_mul, MvPolynomial.aeval_X, PDiv.dUnit, AugCot.d_mul, counit_aeval, hx, zero_smul,
      add_zero]

theorem d_ev (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  obtain ⟨P, a, h1, -, h3⟩ := (exists_split c) n n f
  have h4 : AugCot.d (Bialgebra.counitAlgHom O (G.A n)) ((p : G.A n) ^ n * a) = 0 := by
    rw [show (p : G.A n) ^ n * a = ((p : O) ^ n) • a by
      rw [Algebra.smul_def, map_pow, map_natCast], map_smul]
    exact G.pow_smul_cot n _
  rw [h1, PDiv.dUnit, map_add, h4, add_zero, ← PDiv.dUnit, (d_aeval c)]
  simp only [h3]

theorem coeff_single_of_mem_sq {h : MvPowerSeries (Fin d) O}
    (hh : h ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) (i : Fin d) :
    coeff (Finsupp.single i 1) h = 0 := by
  rw [pow_two] at hh
  refine Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun f g hf hg => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg := congrArg Finsupp.degree hq
    rw [map_add, Finsupp.degree_single] at hdeg
    rcases (show q.1.degree = 0 ∨ q.2.degree = 0 by omega) with h0 | h0
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hf, zero_mul]
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hg, mul_zero]
  · rw [map_add, hf, hg, add_zero]

def lvl (n : ℕ) : (Fin d → O) →ₗ[O] PDiv.Cot O (G.A n) :=
  Fintype.linearCombination O fun i => PDiv.dUnit O (c.x n i)

theorem lvl_apply (n : ℕ) (a : Fin d → O) :
    lvl c n a = ∑ i, a i • PDiv.dUnit O (c.x n i) := Fintype.linearCombination_apply ..

theorem val_comb (a : Fin d → O) (n : ℕ) :
    (Fintype.linearCombination O c.form a).1 n = lvl c n a := by
  rw [Fintype.linearCombination_apply, lvl_apply]
  simp [QLog.Chart.form]

theorem res_lvl (n : ℕ) (a : Fin d → O) :
    PDiv.cotMap (G.res n) (lvl c (n + 1) a) = lvl c n a := by
  simp [lvl_apply, map_sum, map_smul, PDiv.cotMap_d, c.res]

theorem lvl_le (w : G.omega) (a : Fin d → O) {n k : ℕ} (h : n ≤ k)
    (hk : lvl c k a = w.1 k) : lvl c n a = w.1 n := by
  revert hk
  induction k, h using Nat.le_induction with
  | base => exact id
  | succ k hnk ih => exact fun hk => ih (by rw [← res_lvl c, hk, w.2 k])

theorem exists_level_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (m : ℕ) :
    ∃ n, ∀ a : Fin d → O, lvl c n a = 0 → ∀ i, (p : O) ^ m ∣ a i := by
  obtain ⟨n, hn⟩ := c.ker m 2
  refine ⟨n, fun a ha i => ?_⟩
  set y : G.A n := ∑ j, a j • c.x n j with hy0
  have hx : ∀ j, Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := fun j => by
    simpa using c.aug n j
  have hεy : Bialgebra.counitAlgHom O (G.A n) y = 0 := by
    simp [hy0, map_sum, map_smul, hx]
  have hy : PDiv.dUnit O y = 0 := by
    rw [hy0, PDiv.dUnit, map_sum]
    simpa [map_smul, lvl_apply] using ha
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff, hεy, map_zero, sub_zero] at hy
  have hI : RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ≤
      Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O)) := by
    intro z hz
    obtain ⟨g, rfl⟩ := c.surj n z
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, ← counit_ev c]
    exact hz
  have hy2 : y ∈ Ideal.map (c.ev n)
      (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hI 2 hy
  obtain ⟨h, hh, hev⟩ := (Ideal.mem_map_iff_of_surjective _ (c.surj n)).1 hy2
  have hz : c.ev n ((∑ j, a j • X j) - h) = 0 := by
    rw [map_sub, hev, map_sum, hy0]
    simp [map_smul, (c.isEval n).1]
  have := hn _ hz (Finsupp.single i 1) (by simp)
  rw [map_sub, coeff_single_of_mem_sq hh, sub_zero] at this
  classical
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero] using this

theorem comb_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (Fintype.linearCombination O c.form) := by
  choose nm hnm using (exists_level_dvd c)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    funext i
    refine eq_zero_of_dvd _ fun m => hnm m a ?_ i
    rw [← val_comb c, ha]
    rfl
  · intro w
    have hb : ∀ k, ∃ b : Fin d → O, lvl c k b = w.1 k := by
      intro k
      obtain ⟨y, hy⟩ := AugCot.d_surjective _ (w.1 k)
      obtain ⟨g, rfl⟩ := c.surj k y
      exact ⟨lin g, by rw [lvl_apply, ← d_ev c]; exact hy⟩
    choose b hb using hb
    let K : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nm j
    have hK : ∀ {m n}, m ≤ n → K m ≤ K n := fun h =>
      add_le_add h (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h)))
    have hnK : ∀ m, nm m ≤ K m := fun m =>
      le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nm j))
        (Finset.self_mem_range_succ m))
    have hnK' : ∀ m, m ≤ K m := fun m => Nat.le_add_right _ _
    have hcauchy : ∀ {m n}, m ≤ n → ∀ i, (p : O) ^ m ∣ b (K m) i - b (K n) i := by
      intro m n hmn i
      refine hnm m (b (K m) - b (K n)) ?_ i
      rw [map_sub, (lvl_le c) w _ (hnK m) (hb _), (lvl_le c) w _ ((hnK m).trans (hK hmn)) (hb _),
        sub_self]
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ b (K n) i - L := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)})
        (fun m => b (K m) i) fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          exact hcauchy hmn i
      refine ⟨L, fun n => ?_⟩
      have h1 := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h1
      exact h1
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Fintype.linearCombination O c.form L).1 n = w.1 n
    rw [(val_comb c)]
    choose v hv using fun i => hL i n
    have hLv : L = b (K n) - (p : O) ^ n • v := by
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv i]
      ring
    rw [hLv, map_sub, map_smul, G.pow_smul_cot, sub_zero]
    exact (lvl_le c) w _ (hnK' n) (hb _)

end GlobalTheory.ChartForm

theorem GlobalTheory.chart_form_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c
  exact ⟨ChartForm.comb_bijective c, fun n f _ => ChartForm.d_ev c n f⟩
end
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit O (c.ev n f) = ∑ i, lin f i • PDiv.dUnit O (c.x n i) := by
  atlas_forward_decl GlobalTheory.chart_form_basis
end

section
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.PDivGroup.DimSum

theorem baseChange_bijective_of_ker {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : Type) [CommRing k] [Algebra O k] (a : O)
    (ha : algebraMap O k a = 0) (f : M →ₗ[O] N) (hf : Function.Surjective f)
    (hfa : ∀ v, f (a • v) = 0) (hk : ∀ w, f w = 0 → ∃ v, w = a • v) :
    Function.Bijective (f.baseChange k) := by
  rw [LinearMap.baseChange_eq_ltensor]
  refine ⟨?_, LinearMap.lTensor_surjective k hf⟩
  have hex : Function.Exact (a • LinearMap.id : M →ₗ[O] M) f := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, rfl⟩ := hk w hw
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact hfa v
  have hex' := lTensor_exact k hex hf
  have hz : LinearMap.lTensor k (a • LinearMap.id : M →ₗ[O] M) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ha, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex' x).1 hx
  rw [hz, LinearMap.zero_apply]

open GlobalTheory.PDiv Module

theorem finrank_cot_baseChange_one {p : ℕ} {O : Type} [CommRing O] (H : PDivGroup p O) (k : Type)
    [Field k] [Algebra O k] (hp : algebraMap O k p = 0) :
    finrank k (Cot k (k ⊗[O] H.A 1)) = finrank k (k ⊗[O] H.omega) := by
  have h1 : Function.Bijective ((H.omegaLevel 1).baseChange k) :=
    baseChange_bijective_of_ker k (p : O) hp (H.omegaLevel 1) (H.omegaLevel_surjective 1)
      (fun v => by
        have := H.pow_smul_cot 1 (v.1 1)
        rw [pow_one] at this
        exact this)
      (fun w hw => by
        obtain ⟨v, hv⟩ := (H.omega_val_eq_zero_iff 1 w).1 hw
        exact ⟨v, by rw [hv, pow_one]⟩)
  let e1 := LinearEquiv.ofBijective _ h1
  let e2 := LinearEquiv.ofBijective _ (liftSemi_toBaseChange_cot_bijective O k (H.A 1))
  exact (e1.trans e2).finrank_eq.symm

theorem finrank_cot_congr {k X Y : Type} [Field k] [CommRing X] [CommRing Y] [Bialgebra k X]
    [Bialgebra k Y] (e : X ≃ₐc[k] Y) : finrank k (Cot k X) = finrank k (Cot k Y) := by
  have h1 : (e.symm : Y →ₐc[k] X).comp (e : X →ₐc[k] Y) = BialgHom.id k X :=
    BialgHom.ext fun x => e.symm_apply_apply x
  have h2 : (e : X →ₐc[k] Y).comp (e.symm : Y →ₐc[k] X) = BialgHom.id k Y :=
    BialgHom.ext fun x => e.apply_symm_apply x
  refine (LinearEquiv.ofLinear (cotMap (e : X →ₐc[k] Y)) (cotMap (e.symm : Y →ₐc[k] X)) ?_ ?_).finrank_eq
  · rw [← cotMap_comp, h2, cotMap_id]
  · rw [← cotMap_comp, h1, cotMap_id]

end GlobalTheory.PDivGroup.DimSum

open Module PDiv in

theorem GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
      d + Module.finrank O G.dual.Lie = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let k := IsLocalRing.ResidueField O
  have hpk : algebraMap O k p = 0 := by
    change IsLocalRing.residue O p = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : O))
  have hpk' : ((p : ℕ) : k) = 0 := by rw [← map_natCast (algebraMap O k), hpk]
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let eG : (Fin d → O) ≃ₗ[O] G.omega := LinearEquiv.ofBijective _ hbij
  haveI : Module.Free O G.omega := Module.Free.of_equiv eG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  have hd : finrank O G.omega = d := by rw [← eG.finrank_eq, Module.finrank_fin_fun]
  have hLie : finrank O G.dual.Lie = finrank O G.dual.omega := by
    let b := Module.Free.chooseBasis O G.dual.omega
    rw [finrank_eq_card_basis b.dualBasis, finrank_eq_card_basis b]
  obtain ⟨-, -, -, hsum⟩ := finrank_rigExt_omega p k hpk' (G.baseChange k)
  have hA : finrank k (G.baseChange k).omega = finrank O G.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).omegaLevel_one_bijective hpk')).finrank_eq]
    exact (DimSum.finrank_cot_baseChange_one G k hpk).trans (Module.finrank_baseChange)
  have hB : finrank k (G.baseChange k).dual.omega = finrank O G.dual.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).dual.omegaLevel_one_bijective hpk')).finrank_eq]
    refine (DimSum.finrank_cot_congr (CartierDual.baseChange O k (G.A 1))).symm.trans ?_
    exact (DimSum.finrank_cot_baseChange_one G.dual k hpk).trans (Module.finrank_baseChange)
  rw [hLie, ← hd, ← hA, ← hB]
  exact hsum
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), d + Module.finrank O G.dual.Lie = G.height := by
  atlas_forward_decl GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie
end
