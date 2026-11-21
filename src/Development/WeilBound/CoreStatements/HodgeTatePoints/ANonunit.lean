import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowers
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgrROm
import Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalCharacterStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupTranslation
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusProduct
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rom

private theorem prime_pow_le_sum_mul_pow_of_modEq (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (e : Fin f → ℕ) (he : 2 ≤ ∑ i, e i)
    (hc : ∑ i, e i * p ^ (i : ℕ) ≡ p ^ (n + 1) [MOD p ^ f - 1]) :
    p ^ f ≤ ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f) := by
  have hp2 := hp.two_le
  have hq : 2 ≤ p ^ f := le_trans hp2 (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf)
  set M := p ^ f - 1 with hM
  set S := ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f) with hS
  have hpf : (p : ZMod M) ^ f = 1 := by
    have h1 : p ^ f ≡ 1 [MOD M] := Nat.modEq_sub (by omega)
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    push_cast at this
    exact this
  have hcop : Nat.Coprime M (p ^ (n + 1)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h3 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h2 hd
    have h4 : p ^ f - (p ^ f - 1) = 1 := by omega
    rw [h4] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  have hmul : p ^ (n + 1) * S ≡ p ^ (n + 1) * 1 [MOD M] := by
    rw [mul_one]
    refine Nat.ModEq.trans ?_ hc
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hS]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hi := i.isLt
    have hdm := Nat.div_add_mod (n + f - i) f
    have hr := Nat.mod_lt (n + f - i) (by omega : f > 0)
    have hexp : n + 1 + (f - 1 - (n + f - i) % f) = (i : ℕ) + f * ((n + f - i) / f) := by omega
    rw [mul_left_comm, ← pow_add, hexp, pow_add, pow_mul, hpf, one_pow, mul_one]
  have hS1 : S ≡ 1 [MOD M] := Nat.ModEq.cancel_left_of_coprime hcop hmul
  have hS2 : 2 ≤ S := by
    refine le_trans he (Finset.sum_le_sum (fun i _ => ?_))
    exact Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
  by_contra hlt
  push_neg at hlt
  unfold Nat.ModEq at hS1
  rcases Nat.lt_or_ge S M with h | h
  · rw [Nat.mod_eq_of_lt h] at hS1
    rw [Nat.mod_eq_of_lt (by omega)] at hS1
    omega
  · have : S = M := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hS1
    omega

private theorem prod_pow_le_pow_of_frobenius_le (p f n : ℕ) (hp : 1 ≤ p) (hf : 1 ≤ f) (a : ℕ → NNReal) (h1 : ∀ m, a m ≤ 1)
    (hs : ∀ m, a m ^ p ≤ a (m + 1)) (hper : ∀ m, a (m % f) = a m) (e : Fin f → ℕ)
    (hS : p ^ f ≤ ∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f)) :
    ∏ i : Fin f, a i ^ e i ≤ a n ^ p := by
  have hit : ∀ t m, a m ^ (p ^ t) ≤ a (m + t) := by
    intro t
    induction t with
    | zero => intro m; simp
    | succ t ih =>
      intro m
      rw [pow_succ, pow_mul]
      calc (a m ^ p ^ t) ^ p ≤ a (m + t) ^ p := pow_le_pow_left₀ (zero_le) (ih m) p
        _ ≤ a (m + t + 1) := hs _
        _ = a (m + (t + 1)) := by rw [add_assoc]
  have hi : ∀ i : Fin f, a i ^ p ^ ((n + f - i) % f) ≤ a n := by
    intro i
    refine le_trans (hit _ _) (le_of_eq ?_)
    have hil := i.isLt
    have hmod : ((i : ℕ) + (n + f - i) % f) % f = n % f := by
      have h2 : (i : ℕ) + (n + f - i) % f ≡ (i : ℕ) + (n + f - i) [MOD f] :=
        Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
      have h3 : (i : ℕ) + (n + f - i) = n + f := by omega
      rw [h3] at h2
      unfold Nat.ModEq at h2
      rw [h2, Nat.add_mod_right]
    rw [← hper, hmod, hper]
  have hP : p ^ (f - 1) ≠ 0 := pow_ne_zero _ (by omega)
  rw [← pow_le_pow_iff_left₀ (zero_le) (zero_le) hP, ← Finset.prod_pow]
  calc ∏ i : Fin f, (a i ^ e i) ^ p ^ (f - 1)
      ≤ ∏ i : Fin f, a n ^ (e i * p ^ (f - 1 - (n + f - i) % f)) := by
        refine Finset.prod_le_prod' (fun i _ => ?_)
        have hil := i.isLt
        have hr := Nat.mod_lt (n + f - i) (by omega : f > 0)
        have hsplit : p ^ (f - 1) = p ^ ((n + f - i) % f) * p ^ (f - 1 - (n + f - i) % f) := by
          rw [← pow_add]; congr 1; omega
        rw [← pow_mul, hsplit, mul_left_comm, pow_mul]
        exact pow_le_pow_left₀ (zero_le) (hi i) _
    _ = a n ^ (∑ i : Fin f, e i * p ^ (f - 1 - (n + f - i) % f)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ a n ^ (p ^ f) := pow_le_pow_of_le_one (zero_le) (h1 n) hS
    _ = (a n ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']; congr 2; omega

open PositivityTheory.Xgn.A_xgr_r_om PositivityTheory.HtPt.Rb in
theorem r_om_of (h : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_powers) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → ∀ n, (∀ r : R, (fun a => algebraMap R C (r * (σ ^ p ^ (n + 1)) a)) ∈ sqIdeal (augIdeal AA.carrier) ↔ r ∈ Ideal.span {c n ^ p}) ∧ (∃ δ : R, c n ^ p = δ * c (n + 1)) ∧ ∀ δ : R, c n ^ p = δ * c (n + 1) → HasLen v R (OmType AA.carrier (σ ^ p ^ (n + 1))) (v (algebraMap R C δ)) := by
  intro p hpp C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard AA hst σ hσ c hc n
  have hpr : p.Prime := hpp.out
  have hp2 := hpr.two_le
  obtain ⟨hord, -, -, -, -⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hp F f hcard σ hσ
  obtain ⟨hval, hprod⟩ := h p C v R hv hp F f hcard AA hst σ hσ c hc
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 := Fintype.one_lt_card (α := F)
      rw [hcard, h0, pow_zero] at h1
      omega
    · exact h0
  obtain ⟨hcardne, w, hw⟩ := exists_inv_card (F := F) hv hp hcard
  have hvp : v (p : C) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hpr.ne_zero
  have hcne : ∀ m, c m ≠ 0 := by
    intro m hm
    have h1 := (hval m)
    rw [hm, map_zero, map_zero, zero_pow (by omega)] at h1
    exact hvp (le_antisymm h1 (zero_le))
  have hstep : ∀ m, c m ^ p ∈ Ideal.span {c (m + 1)} := by
    intro m
    rw [← hc (m + 1), mem_x_ideal_iff]
    have h1 := pow_mem_sq AA (σ ^ p ^ m) (c := c m) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2
    rw [← pow_mul, ← pow_succ] at h1
    exact sq_le AA h1
  have hper : ∀ m, σ ^ p ^ (m % f) = σ ^ p ^ m := by
    intro m
    rw [pow_eq_pow_iff_modEq, hord, ← ZMod.natCast_eq_natCast_iff]
    have h1 : p ^ f ≡ 1 [MOD p ^ f - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    push_cast at h2 ⊢
    conv_rhs => rw [← Nat.mod_add_div m f, pow_add, pow_mul, h2, one_pow, mul_one]
  set a : ℕ → NNReal := fun m => v (algebraMap R C (c m)) with ha
  have ha1 : ∀ m, a m ≤ 1 := fun m => hv.map_le_one _
  have has : ∀ m, a m ^ p ≤ a (m + 1) := by
    intro m
    have h1 := hv.le_of_dvd (Ideal.mem_span_singleton.1 (hstep m))
    simp only [ha, map_pow] at h1 ⊢
    exact h1
  have haper : ∀ m, a (m % f) = a m := by
    intro m
    exact v_eq_of_span hv (by rw [← hc, ← hc, hper])
  have hE : ∀ m, 1 ≤ m → m ≤ p ^ f - 1 → ∀ e ∈ eig AA.carrier (σ ^ m), ∃ d : Fin f → Fin p,
      (∃ i, (d i : ℕ) ≠ 0) ∧ ∑ i : Fin f, (d i : ℕ) * p ^ (i : ℕ) = m ∧
      v (e 1) ≤ ∏ i : Fin f, a i ^ (d i : ℕ) := by
    intro m hm1 hm2 e he
    have he' : e ∈ AA.carrier ∧ ∀ (x : F) (y : F), e (x • y) = algebraMap R C ((σ ^ m) x) * e y := he
    obtain ⟨d, hd0, hdm⟩ := digits (p := p) (f := f) hm1 (by have := Nat.one_le_pow f p (by omega); omega)
    refine ⟨d, hd0, hdm, ?_⟩
    obtain ⟨t, ht⟩ := AA.le_int he'.1 1
    have hfun : (fun x : F => algebraMap R C (t * (σ ^ m) x)) = e := by
      funext x
      have := he'.2 x 1
      rw [smul_eq_mul, mul_one] at this
      rw [this, ← ht, map_mul, mul_comm]
    have htm : t ∈ xIdeal AA.carrier (σ ^ m) := by
      rw [mem_x_ideal_iff, hfun]; exact he'.1
    rw [← hdm, hprod d hd0] at htm
    rw [← ht]
    refine le_trans (v_le_of_mem hv htm) (le_of_eq ?_)
    simp only [ha, map_prod, map_pow]
  set χ : MulChar F R := σ ^ p ^ (n + 1) with hχdef
  set L : (F → C) →ₗ[R] C := (LinearMap.proj (R := R) (φ := fun _ : F => C) (1 : F)).comp (projL χ) with hL
  have hLapp : ∀ g, L g = proj χ g 1 := by
    intro g; simp [hL, projL_apply]
  have hbound : ∀ g ∈ augIdeal AA.carrier, ∀ g' ∈ augIdeal AA.carrier, v (L (g * g')) ≤ a n ^ p := by
    intro g hg g' hg'
    obtain ⟨hPg, hsum, -⟩ := proj_props p C v R hv hp F f hcard F AA hst σ hσ g hg
    obtain ⟨hPg', hsum', -⟩ := proj_props p C v R hv hp F f hcard F AA hst σ hσ g' hg'
    have hgg : g * g' = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), ∑ m' ∈ Finset.Icc 1 (p ^ f - 1),
        proj (σ ^ m) g * proj (σ ^ m') g' := by
      conv_lhs => rw [hsum, hsum']
      rw [Finset.sum_mul_sum]
    rw [hgg, map_sum]
    refine Valuation.map_sum_le _ (fun m hm => ?_)
    rw [map_sum]
    refine Valuation.map_sum_le _ (fun m' hm' => ?_)
    rw [Finset.mem_Icc] at hm hm'
    have e1 : proj (σ ^ m) g ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m) g (x • y) = algebraMap R C ((σ ^ m) x) * proj (σ ^ m) g y := hPg (σ ^ m)
    have e2 : proj (σ ^ m') g' ∈ AA.carrier ∧ ∀ (x : F) (y : F), proj (σ ^ m') g' (x • y) = algebraMap R C ((σ ^ m') x) * proj (σ ^ m') g' y := hPg' (σ ^ m')
    have heig : ∀ (x : F) (y : F), (proj (σ ^ m) g * proj (σ ^ m') g') (x • y) =
        algebraMap R C ((σ ^ m * σ ^ m') x) * (proj (σ ^ m) g * proj (σ ^ m') g') y := by
      intro x y
      simp only [Pi.mul_apply, e1.2, e2.2, MulChar.mul_apply, map_mul]
      ring
    by_cases hχ : σ ^ m * σ ^ m' = χ
    · rw [hLapp, proj_eigen_self hcardne χ _ (by rw [← hχ]; exact heig), Pi.mul_apply, map_mul]
      obtain ⟨d, hd0, hdm, hdv⟩ := hE m hm.1 hm.2 _ (hPg (σ ^ m))
      obtain ⟨d', hd0', hdm', hdv'⟩ := hE m' hm'.1 hm'.2 _ (hPg' (σ ^ m'))
      refine le_trans (mul_le_mul' hdv hdv') ?_
      rw [← Finset.prod_mul_distrib]
      simp only [← pow_add]
      refine prod_pow_le_pow_of_frobenius_le p f n (by omega) hf1 a ha1 has haper (fun i => (d i : ℕ) + d' i) ?_
      refine prime_pow_le_sum_mul_pow_of_modEq p f n hpr hf1 _ ?_ ?_
      · obtain ⟨i, hi⟩ := hd0
        obtain ⟨i', hi'⟩ := hd0'
        rw [Finset.sum_add_distrib]
        have h1 := Finset.single_le_sum (f := fun j => ((d j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have h2 := Finset.single_le_sum (f := fun j => ((d' j : Fin p) : ℕ)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i')
        omega
      · simp only [add_mul, Finset.sum_add_distrib, hdm, hdm']
        rw [← hord, ← pow_eq_pow_iff_modEq, pow_add, hχ]
    · rw [hLapp, proj_eigen_ne (Ne.symm hχ) _ heig]
      simp
  have hsqn : (fun x : F => algebraMap R C (c n ^ p * χ x)) ∈ sqIdeal (augIdeal AA.carrier) := by
    have h1 := pow_mem_sq AA (σ ^ p ^ n) (c := c n) (by rw [hc]; exact Ideal.mem_span_singleton_self _) (k := p) hp2
    rw [← pow_mul, ← pow_succ] at h1
    exact h1
  have hP1 : ∀ r : R, (fun x : F => algebraMap R C (r * χ x)) ∈ sqIdeal (augIdeal AA.carrier) ↔
      r ∈ Ideal.span {c n ^ p} := by
    intro r
    constructor
    · intro hr
      have h1 := sq_bound hv (augIdeal AA.carrier : Set (F → C)) L (a n ^ p)
        (fun g hg g' hg' => hbound g hg g' hg') _ (by rwa [Submodule.span_eq])
      rw [hLapp, proj_eigen_self hcardne χ _ (fun x y => eig_fun χ r x y), MulChar.map_one, mul_one] at h1
      rw [Ideal.mem_span_singleton]
      refine hv.dvd_of_le ?_
      simpa [ha, map_pow] using h1
    · intro hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      have : (fun x : F => algebraMap R C (s * c n ^ p * χ x)) = s • (fun x : F => algebraMap R C (c n ^ p * χ x)) := by
        funext x; simp [Algebra.smul_def, mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ _ hsqn
  refine ⟨hP1, ?_, ?_⟩
  · obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    exact ⟨δ, hδ.symm⟩
  · intro δ hδ
    set e0 : F → C := fun x => algebraMap R C (c (n + 1) * χ x) with he0def
    have he0 : e0 ∈ eig AA.carrier χ := by
      show e0 ∈ AA.carrier ∧ ∀ (x y : F), e0 (x • y) = algebraMap R C (χ x) * e0 y
      exact ⟨(mem_x_ideal_iff _ _ _).1 (by rw [hc]; exact Ideal.mem_span_singleton_self _),
        fun x y => eig_fun χ _ x y⟩
    let φ : R →ₗ[R] OmType AA.carrier χ :=
      (Submodule.mkQ _).comp (LinearMap.toSpanSingleton R _ (⟨e0, he0⟩ : eig AA.carrier χ))
    have hφ : ∀ r, φ r = Submodule.Quotient.mk (r • (⟨e0, he0⟩ : eig AA.carrier χ)) := fun r => rfl
    refine hasLen_quot v φ ?_ δ ?_
    · intro x
      induction x using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨y, hy⟩ := y
        have hy' : y ∈ AA.carrier ∧ ∀ (x z : F), y (x • z) = algebraMap R C (χ x) * y z := hy
        obtain ⟨t, ht⟩ := AA.le_int hy'.1 1
        have hfun : (fun x : F => algebraMap R C (t * χ x)) = y := by
          funext x
          have := hy'.2 x 1
          rw [smul_eq_mul, mul_one] at this
          rw [this, ← ht, map_mul, mul_comm]
        have htm : t ∈ xIdeal AA.carrier χ := by
          rw [mem_x_ideal_iff, hfun]; exact hy'.1
        rw [hc] at htm
        obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 htm
        refine ⟨s, ?_⟩
        rw [hφ]
        congr 1
        apply Subtype.ext
        show ((s • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) = y
        rw [← hfun]
        funext x
        simp [he0def, Algebra.smul_def, mul_assoc]
    · ext r
      rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      have hfun : ((r • (⟨e0, he0⟩ : eig AA.carrier χ) : eig AA.carrier χ) : F → C) =
          (fun x : F => algebraMap R C (r * c (n + 1) * χ x)) := by
        funext x
        simp [he0def, Algebra.smul_def, mul_assoc]
      rw [Submodule.subtype_apply, hfun, hP1, hδ, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        mul_dvd_mul_iff_right (hcne (n + 1))]

end PositivityTheory.HtPt.Rom
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem sq_le_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)}
    (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) : sqIdeal (augIdeal M) ≤ augIdeal M := by
  rw [sqIdeal, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine mem_aug.2 ⟨hmul a ha.1 b hb.1, ?_⟩
  rw [Pi.mul_apply, (mem_aug.1 ha).2, zero_mul]

theorem adjoin_decomp (p : ℕ) {N : Type} [AddCommGroup N] {M : Submodule R (N → C)}
    (hone : (1 : N → C) ∈ M) (hmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) (hint : M ≤ intFun R N)
    {g : N → C} (hg : g ∈ Algebra.adjoin R ((afFun p M : Submodule R (N → C)) : Set (N → C))) :
    ∃ r : R, ∃ h ∈ afFun p M ⊓ augIdeal M, ∃ w ∈ sqIdeal (augIdeal M),
      g = r • (1 : N → C) + h + w := by
  induction hg using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨hg, hadd⟩ := hg
    obtain ⟨r, hr⟩ := hint hg 0
    have hval : ∀ x, (g - r • (1 : N → C)) x = g x - g 0 := fun x => by
      simp [Algebra.smul_def, hr]
    have hm : g - r • (1 : N → C) ∈ M := M.sub_mem hg (M.smul_mem r hone)
    refine ⟨r, g - r • (1 : N → C), ⟨⟨hm, fun x y => ?_⟩, mem_aug.2 ⟨hm, ?_⟩⟩, 0,
      Submodule.zero_mem _, by abel⟩
    · have := Submodule.sub_mem _ (hadd x y) (hadd 0 0)
      convert this using 1
      simp only [hval, add_zero]; ring
    · rw [hval, sub_self]
  | algebraMap r =>
    exact ⟨r, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by
      rw [add_zero, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  | add a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    exact ⟨r + r', h + h', Submodule.add_mem _ hh hh', w + w', Submodule.add_mem _ hw hw', by
      rw [add_smul]; abel⟩
  | mul a b _ _ ha hb =>
    obtain ⟨r, h, hh, w, hw, rfl⟩ := ha
    obtain ⟨r', h', hh', w', hw', rfl⟩ := hb
    refine ⟨r * r', r • h' + r' • h,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hh') (Submodule.smul_mem _ _ hh),
      r • w' + r' • w + (h + w) * (h' + w'),
      Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hw')
        (Submodule.smul_mem _ _ hw)) (Submodule.subset_span
          ⟨h + w, Submodule.add_mem _ hh.2 (sq_le_aug hmul hw),
            h' + w', Submodule.add_mem _ hh'.2 (sq_le_aug hmul hw'), rfl⟩), ?_⟩
    simp only [Algebra.smul_def, map_mul]
    ring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {N : Type} [AddCommGroup N] [Module F N]

theorem proj_add (χ : MulChar F R) (g h : N → C) (x : N) :
    proj χ (g + h) x = proj χ g x + proj χ h x := by
  simp only [proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem proj_line (χ : MulChar F R) (g : N → C) (t : N) :
    proj χ (g ∘ LinearMap.toSpanSingleton F N t) 1 = proj χ g t := by
  simp [proj]

theorem proj_self [CharZero C] (χ : MulChar F R) (g : N → C) (t : N) (c : R)
    (hg : ∀ a : F, g (a • t) = algebraMap R C (c * χ a)) : proj χ g t = algebraMap R C c := by
  have h1 : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • t) = algebraMap R C c := by
    intro a
    have : χ⁻¹ (a : F) * χ a = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
    rw [hg, ← map_mul, mul_left_comm, this, mul_one]
  have h0 : (Fintype.card Fˣ : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [proj, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

end

theorem a_nonunit_of (hproj : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_character) (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation)
    (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t ht hgen τ hτ c' c hc' hc hlt
  obtain ⟨⟨S, hS, hSst⟩, -⟩ := hstep p C v R hv hp1 F f hF N AA hst K t ht
  have hprin := GlobalTheory.T.character_ideal_principal_eigen p C v R hv hp1 F f hF S hSst
  choose cc hcc0 hcc using fun χ => (hprin χ).1
  have hcm : c ∈ idealX AA.carrier K t (τ ^ p) := by rw [hc]; exact Ideal.mem_span_singleton_self c
  obtain ⟨g₀, hg₀, e₀⟩ := hcm
  have e1 : ∀ a : F, g₀ (a • t) = algebraMap R C (c * (τ ^ p) a) := fun a => by
    have := congrFun e₀ a
    simpa [LinearMap.funLeft_apply, Algebra.smul_def] using this
  have hmul : ∀ a ∈ invFun AA.carrier K.toAddSubgroup, ∀ b ∈ invFun AA.carrier K.toAddSubgroup,
      a * b ∈ invFun AA.carrier K.toAddSubgroup := fun a ha b hb =>
    ⟨AA.mul_mem a b ha.1 hb.1, fun x k hk => by
      rw [Pi.mul_apply, Pi.mul_apply, ha.2 x k hk, hb.2 x k hk]⟩
  obtain ⟨r, h, ⟨hh, hh0⟩, w, hw, e⟩ := adjoin_decomp p (M := invFun AA.carrier K.toAddSubgroup)
    ⟨AA.one_mem, fun _ _ _ => rfl⟩ hmul (fun a ha => AA.le_int ha.1) (hgen hg₀)
  have hw0 := (mem_aug.1 (sq_le_aug hmul hw)).2
  have hr : r • (1 : N → C) = 0 := by
    have h1 := congrFun e 0
    have h2 := e1 0
    rw [zero_smul, MulChar.map_zero, mul_zero, map_zero] at h2
    rw [h2, Pi.add_apply, Pi.add_apply, (mem_aug.1 hh0).2, hw0, add_zero, add_zero] at h1
    funext x
    exact h1.symm
  rw [hr, zero_add] at e
  have hwS : w ∘ LinearMap.toSpanSingleton F N t ∈ sqIdeal (augIdeal S.carrier) :=
    sq_pull _ (fun g hg => by rw [hS]; exact ⟨g, hg, rfl⟩) hw
  have hwS' := sq_le_aug (fun a ha b hb => S.mul_mem a b ha hb) hwS
  obtain ⟨w1, -, -, -, w5⟩ := hproj p C v R hv hp1 F f hF F S hSst τ hτ _ hwS'
  obtain ⟨ρ, -, hρ⟩ := ((hprin (τ ^ p)).2 _).1 (w1 (τ ^ p))
  have hρ1 := w5 hwS (τ ^ p)
  have hρ2 : ρ ∈ Ideal.span {cc (τ ^ p ^ 0) ^ p} := by
    refine ((hom p C v R hv hp1 F f hF S hSst τ hτ (fun n => cc (τ ^ p ^ n)) (fun n => hcc _)
      0).1 ρ).1 ?_
    rw [zero_add, pow_one, ← hρ]
    exact hρ1
  have hcc' : cc (τ ^ p ^ 0) ∈ Ideal.span {c'} := by
    rw [← hc', idealX, ← hS, pow_zero, pow_one, hcc]
    exact Ideal.mem_span_singleton_self _
  have hρ3 : v (algebraMap R C ρ) < v (algebraMap R C c) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [← map_pow, ← map_pow]
    exact hv.le_of_dvd ((pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hcc') p).trans
      (Ideal.mem_span_singleton.1 hρ2))
  have hwt : proj (τ ^ p) w t = algebraMap R C ρ := by
    rw [← proj_line, hρ]
    simp
  have hht : proj (τ ^ p) h t = algebraMap R C (c - ρ) := by
    have := proj_self (τ ^ p) g₀ t c e1
    rw [e, proj_add, hwt] at this
    rw [map_sub, ← this, add_sub_cancel_right]
  obtain ⟨q1, -, q3, q4, -⟩ := hproj p C v R hv hp1 F f hF N AA hst τ hτ h
    (mem_aug.2 ⟨hh.1.1, (mem_aug.1 hh0).2⟩)
  have hD : c - ρ ∈ idealD p AA.carrier K t (τ ^ p) := by
    refine ⟨proj (τ ^ p) h, q3 ⟨hh.1.1, hh.2⟩ _, fun a x => ?_, fun k hk => ?_, ?_⟩
    · rw [(q1 (τ ^ p)).2 a x, sub_self]; exact Submodule.zero_mem _
    · have := (q4 K hh.1 (τ ^ p)).2 0 k hk
      rw [zero_add, eig_zero (q1 (τ ^ p))] at this
      rw [this]; exact Submodule.zero_mem _
    · rw [hht, sub_self]; exact Submodule.zero_mem _
  have hdvd : c - ρ ∣ c := by
    apply hv.dvd_of_le
    rw [map_sub, v.map_sub_eq_of_lt_left hρ3]
  exact Ideal.mem_of_dvd _ hdvd hD

end PositivityTheory.HtPt.Rd
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem a_nonunit_rom_of (hom : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_product) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  a_nonunit_of @PositivityTheory.HtPt.Rb.proj_props @PositivityTheory.HtPt.Rc.step hom

end PositivityTheory.HtPt.Rd
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rom

theorem a_nonunit_of (h : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_powers) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  PositivityTheory.HtPt.Rd.a_nonunit_rom_of (@r_om_of h)

end PositivityTheory.HtPt.Rom
end

section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rfin

theorem a_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  Rom.a_nonunit_of @Pmono.r_mono

end PositivityTheory.HtPt.Rfin
end
