import Mathlib
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

private theorem mem_span_of_step {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    x ∈ span {a} := by
  choose Y X hYX using h
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → {z // P z}, g 0 = ⟨x, hx⟩ ∧
      ∀ n, g (n + 1) = ⟨X (g n).1 (g n).2, (hYX (g n).1 (g n).2).2⟩ :=
    ⟨fun n => Nat.rec (motive := fun _ => {z // P z}) ⟨x, hx⟩
      (fun _ z => ⟨X z.1 z.2, (hYX z.1 z.2).2⟩) n, rfl, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ → A, ∀ n, (g n).1 = a * y n + q * (g (n + 1)).1 :=
    ⟨fun n => Y (g n).1 (g n).2, fun n => by rw [hgs n]; exact (hYX _ _).1⟩
  have hmem : ∀ (n : ℕ) (z : A), z ∈ ((span {q}) ^ n • ⊤ : Submodule A A) ↔ q ^ n ∣ z := by
    intro n z
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have key : ∀ n, x = a * (∑ i ∈ Finset.range n, q ^ i * y i) + q ^ n * (g n).1 := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [hy n] at ih
      linear_combination ih
  have hcau : ∀ {m n : ℕ}, m ≤ n →
      (∑ i ∈ Finset.range m, q ^ i * y i) ≡ (∑ i ∈ Finset.range n, q ^ i * y i)
        [SMOD ((span {q}) ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hmem]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [Finset.sum_range_add, show ∀ u w : A, u - (u + w) = -w from fun u w => by ring, dvd_neg]
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (pow_dvd_pow q (Nat.le_add_right m j)) _
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {q}) inferInstance
    (f := fun n => ∑ i ∈ Finset.range n, q ^ i * y i) hcau
  have hz : x - a * L = 0 := by
    refine IsHausdorff.haus (I := span {q}) inferInstance _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hmem]
    have hd : q ^ n ∣ (∑ i ∈ Finset.range n, q ^ i * y i) - L :=
      (hmem n _).1 (SModEq.sub_mem.1 (hL n))
    have e : x - a * L = a * ((∑ i ∈ Finset.range n, q ^ i * y i) - L) + q ^ n * (g n).1 := by
      linear_combination key n
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hd a) (dvd_mul_right _ _)
  exact Ideal.mem_span_singleton'.2 ⟨L, by linear_combination -hz⟩

variable {p : ℕ} [hp : Fact p.Prime]

section Sharp

variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

private def sh (x : PreTilt O p) (n : ℕ) : O :=
  (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x).untilt

private theorem sh_pow_succ (x : PreTilt O p) (n : ℕ) : sh x (n + 1) ^ p = sh x n := by
  unfold sh
  rw [Function.iterate_succ_apply', ← map_pow]
  congr 1
  have h := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x)
  rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

private theorem sh_pow (x : PreTilt O p) (n : ℕ) : sh x n ^ p ^ n = x.untilt := by
  induction n with
  | zero => simp [sh]
  | succ n ih => rw [pow_succ', pow_mul, sh_pow_succ, ih]

private theorem preTilt_coeff_succ_pow_p (f : PreTilt O p) (n : ℕ) :
    PreTilt.coeff (n + 1) (f ^ p) = PreTilt.coeff n f := by
  exact Perfection.coeff_pow_p f n

private theorem preTilt_ext_coeff {x y : PreTilt O p} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) :
    x = y := by
  exact Perfection.ext h

private theorem preTilt_coeff_iterate_frobenius_symm (y : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] y) =
      PreTilt.coeff (m + n) y := by
  induction n generalizing y m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    conv_rhs => rw [← (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply y]
    rw [_root_.frobeniusEquiv_apply, frobenius_def, ← Nat.add_assoc]
    exact (preTilt_coeff_succ_pow_p _ _).symm

private theorem witt_exists_eq_teichmuller_coeff_zero_add_p_mul {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (x : WittVector p R) :
    ∃ z, x = teichmuller p (x.coeff 0) + (p : WittVector p R) * z := by
  obtain ⟨w, hw⟩ : ∃ w, w = x - teichmuller p (x.coeff 0) := ⟨_, rfl⟩
  have hx : x = teichmuller p (x.coeff 0) + w := by rw [hw]; ring
  have hw0 : w.coeff 0 = 0 := by
    have h := congrArg (fun y : WittVector p R => y.coeff 0) hx
    simp only [WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero] at h
    linear_combination -h
  by_cases hw' : w = 0
  · refine ⟨0, ?_⟩
    have h1 := hx
    rw [hw', add_zero] at h1
    rw [mul_zero, add_zero]
    exact h1
  · obtain ⟨m, b, hb, hwb⟩ := WittVector.exists_eq_pow_p_mul w hw'
    cases m with
    | zero =>
      rw [pow_zero, one_mul] at hwb
      rw [hwb] at hw0
      exact absurd hw0 hb
    | succ m =>
      refine ⟨(p : WittVector p R) ^ m * b, ?_⟩
      conv_lhs => rw [hx, hwb]
      ring

private theorem mk_sh (x : PreTilt O p) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (sh x n) = PreTilt.coeff n x := by
  unfold sh
  rw [PreTilt.mk_untilt_eq_coeff_zero, preTilt_coeff_iterate_frobenius_symm, Nat.zero_add]

end Sharp

section Ker

variable (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal)
  {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

include hv

private theorem p_ne_zero : (p : O) ≠ 0 := by
  intro h
  have h2 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
  rw [map_natCast] at h2
  exact (Nat.cast_ne_zero.2 hp.out.ne_zero) h2

private theorem torsionFree {a : O} (h : (p : O) * a = 0) : a = 0 := by
  apply hv.hom_inj
  have h2 := congrArg (algebraMap O C) h
  rw [map_mul, map_natCast, map_zero] at h2
  rw [map_zero]
  exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hp.out.ne_zero)

private theorem isDomain_integers : IsDomain O := by
  have : Nontrivial O := ⟨⟨1, 0, fun h => one_ne_zero ((map_one (algebraMap O C)).symm.trans
    ((congrArg (algebraMap O C) h).trans (map_zero _)))⟩⟩
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj

private theorem dvd_of_coeff_zero (pflat : PreTilt O p) (hpf : pflat.untilt = (p : O))
    (c : PreTilt O p) (hc : PreTilt.coeff 0 c = 0) : ∃ d, c = pflat * d := by
  have := isDomain_integers C v hv
  have hpn : (p : O) ≠ 0 := p_ne_zero C v hv
  have hpi : ∀ n, sh pflat n ≠ 0 := by
    intro n h0
    have h1 := sh_pow pflat n
    rw [h0, zero_pow (pow_ne_zero n hp.out.ne_zero), hpf] at h1
    exact hpn h1.symm
  obtain ⟨u, hu⟩ : (p : O) ∣ c.untilt := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    exact (mk_sh c 0).trans hc
  have hdvd : ∀ n, sh pflat n ∣ sh c n := by
    intro n
    apply hv.dvd_of_le
    have h1 : v (algebraMap O C (sh c n)) ^ (p ^ n) ≤
        v (algebraMap O C (sh pflat n)) ^ (p ^ n) := by
      rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sh_pow, sh_pow, hpf, hu, map_mul, map_mul]
      exact mul_le_of_le_one_right zero_le (hv.map_le_one u)
    have hn : p ^ n ≠ 0 := pow_ne_zero n hp.out.ne_zero
    exact (pow_le_pow_iff_left₀ zero_le zero_le hn).1 h1
  choose D hD using hdvd
  have hDp : ∀ n, D (n + 1) ^ p = D n := by
    intro n
    have h1 := sh_pow_succ c n
    rw [hD (n + 1), hD n, mul_pow, sh_pow_succ] at h1
    exact mul_left_cancel₀ (hpi n) h1
  let d : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (span {(p : O)}) (D n),
    fun n => by rw [← map_pow, hDp]⟩
  refine ⟨d, preTilt_ext_coeff fun n => ?_⟩
  have hdn : PreTilt.coeff n d = Ideal.Quotient.mk (span {(p : O)}) (D n) := by
    rfl
  rw [map_mul, hdn, ← mk_sh c n, ← mk_sh pflat n, hD n, map_mul]

private theorem preTilt_eq_zero_of_untilt_eq_zero (x : PreTilt O p) (h : x.untilt = 0) : x = 0 := by
  have hs : ∀ n, sh x n = 0 := by
    intro n
    apply hv.hom_inj
    rw [map_zero]
    have h2 := congrArg (algebraMap O C) (sh_pow x n)
    rw [h, map_zero, map_pow] at h2
    first
    | exact pow_eq_zero h2
    | exact pow_eq_zero_iff (pow_ne_zero n hp.out.ne_zero) |>.1 h2
  apply preTilt_ext_coeff
  intro n
  rw [map_zero, ← mk_sh x n, hs n, map_zero]

theorem kerTheta : KerThetaStatement p O := by
  have := isDomain_integers C v hv
  intro pflat hpf
  have hpn : (p : O) ≠ 0 := p_ne_zero C v hv
  have hθt : ∀ y : PreTilt O p, fontaineTheta O p (teichmuller p y) = y.untilt :=
    fun y => fontaineTheta_teichmuller y
  have hmkp : Ideal.Quotient.mk (span {(p : O)}) (p : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hξ : fontaineTheta O p ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) = 0 := by
    rw [map_sub, map_natCast, hθt, hpf, sub_self]
  have hmod : ∀ x : WittVector p (PreTilt O p),
      Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta O p x) = PreTilt.coeff 0 (x.coeff 0) := by
    intro x
    obtain ⟨z, hz⟩ := witt_exists_eq_teichmuller_coeff_zero_add_p_mul x
    conv_lhs => rw [hz]
    rw [map_add, map_mul, map_natCast, hθt, map_add, map_mul, hmkp, zero_mul, add_zero]
    exact mk_sh (x.coeff 0) 0
  have hfac : ∀ x : WittVector p (PreTilt O p),
      Ideal.Quotient.mk (span {(p : O)}) (fontaineTheta O p x) = 0 →
      ∃ d z, x = teichmuller p pflat * teichmuller p d + (p : WittVector p (PreTilt O p)) * z := by
    intro x hx
    obtain ⟨z, hz⟩ := witt_exists_eq_teichmuller_coeff_zero_add_p_mul x
    rw [hmod] at hx
    obtain ⟨d, hd⟩ := dvd_of_coeff_zero C v hv pflat hpf _ hx
    exact ⟨d, z, by rw [hz, hd, map_mul]⟩
  refine ⟨le_antisymm (fun x hx => ?_) ((Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hξ)),
    ?_, ?_⟩
  · refine mem_span_of_step (p : WittVector p (PreTilt O p)) _
      (fun x => fontaineTheta O p x = 0) ?_ x (RingHom.mem_ker.1 hx)
    intro x (hx0 : fontaineTheta O p x = 0)
    obtain ⟨d, z, hdz⟩ := hfac x (by rw [hx0, map_zero])
    refine ⟨-teichmuller p d, teichmuller p d + z, ?_, ?_⟩
    · rw [hdz]; ring
    · show fontaineTheta O p (teichmuller p d + z) = 0
      apply torsionFree (p := p) C v hv
      have e : (p : WittVector p (PreTilt O p)) * (teichmuller p d + z) =
          x + ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) * teichmuller p d := by
        rw [hdz]; ring
      rw [← map_natCast (fontaineTheta O p) p, ← map_mul, e, map_add, map_mul, hx0, hξ, zero_mul,
        add_zero]
  · have hu0 : PreTilt.untilt (0 : PreTilt O p) = 0 := by
      have e := map_mul PreTilt.untilt (0 : PreTilt O p) pflat
      rw [zero_mul, hpf] at e
      have e2 : PreTilt.untilt (0 : PreTilt O p) * (1 - (p : O)) = 0 := by linear_combination e
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact ((Fact.out : ¬IsUnit (p : O)) (by rw [← sub_eq_zero.1 h]; exact isUnit_one)).elim
    have hnz : ∀ a b : PreTilt O p, a * b = 0 → a = 0 ∨ b = 0 := by
      intro a b hab
      have h1 : a.untilt * b.untilt = 0 := by rw [← map_mul, hab, hu0]
      rcases mul_eq_zero.1 h1 with h | h
      · exact Or.inl (preTilt_eq_zero_of_untilt_eq_zero C v hv a h)
      · exact Or.inr (preTilt_eq_zero_of_untilt_eq_zero C v hv b h)
    have : NoZeroDivisors (PreTilt O p) := ⟨fun {a b} h => hnz a b h⟩
    have hπ : pflat ≠ 0 := fun h => hpn (by rw [← hpf, h, hu0])
    have hne : ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : WittVector p (PreTilt O p) => w.coeff 0) (sub_eq_zero.1 h)
      simp only [WittVector.teichmuller_coeff_zero, WittVector.coeff_p_zero] at h2
      exact hπ h2.symm
    exact mem_nonZeroDivisors_of_ne_zero hne
  · apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply] at hx
      obtain ⟨d, z, hdz⟩ := hfac x hx
      exact Ideal.mem_span_pair.2 ⟨z, teichmuller p d, by rw [hdz]; ring⟩
    · rw [Ideal.span_le]
      intro w hw
      rcases hw with rfl | rfl
      · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, map_natCast, hmkp]
      · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, hθt, hpf, hmkp]

end Ker

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open WittVector Ideal Polynomial

namespace ReciprocityTheory.PGsh

private lemma perfection_isUnit {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) : IsUnit x := by
  have hu : ∀ n, IsUnit (Perfection.coeff R p n x) := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      have h2 : Perfection.coeff R p (n + 1) x ^ p = Perfection.coeff R p n x :=
        Perfection.coeff_pow_p' x n
      rw [← h2] at ih
      exact (isUnit_pow_iff hp.out.ne_zero).mp ih
  have h3 : ∀ n, (hu (n + 1)).unit ^ p = (hu n).unit := fun n =>
    Units.ext (by simpa using Perfection.coeff_pow_p' x n)
  let y : Perfection R p := ⟨fun n => ((hu n).unit⁻¹ : Rˣ), fun n => by
    show (((hu (n + 1)).unit⁻¹ : Rˣ) : R) ^ p = (((hu n).unit⁻¹ : Rˣ) : R)
    rw [← Units.val_pow_eq_pow_val, inv_pow, h3]⟩
  refine isUnit_iff_exists_inv.mpr ⟨y, Perfection.ext fun n => ?_⟩
  rw [map_mul, map_one]
  exact (hu n).mul_val_inv

private lemma witt_isUnit {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    [PerfectRing R p] (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  exact ⟨WittVector.mkUnit (p := p) (a := u) (A := c) (by rw [hu]; rfl), rfl⟩

private lemma sub_one_pow_pred {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : R) : (x - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, x ^ i := by
  have hX : ((Polynomial.X : (ZMod p)[X]) - 1) ^ (p - 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X : (ZMod p)[X]) ^ i := by
    have hne : (Polynomial.X : (ZMod p)[X]) - 1 ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    apply mul_left_cancel₀ hne
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow, mul_comm,
      geom_sum_mul]
  have h := congrArg (Polynomial.eval₂ (ZMod.castHom (dvd_refl p) R) x) hX
  simpa [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_one] using h

private lemma val_sub_one_le {C : Type*} [Field C] (v : Valuation C NNReal) {p : ℕ}
    [hp : Fact p.Prime] {α β : C} (hα : IsPrimitiveRoot α p) (hβ : IsPrimitiveRoot β p) :
    v (α - 1) ≤ v (β - 1) := by
  obtain ⟨i, -, hi⟩ : ∃ i < p, β ^ i = α := by
    first
    | exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one
    | exact hβ.eq_pow_of_pow_eq_one hα.pow_eq_one hp.out.pos
  have hvb : v β = 1 := by
    have h : v β ^ p = 1 := by rw [← map_pow, hβ.pow_eq_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (by positivity) hp.out.ne_zero).mp h
  rw [← hi, ← geom_sum_mul, map_mul]
  have hs : v (∑ k ∈ Finset.range i, β ^ k) ≤ 1 :=
    v.map_sum_le fun k _ => by rw [map_pow, hvb, one_pow]
  calc v (∑ k ∈ Finset.range i, β ^ k) * v (β - 1) ≤ 1 * v (β - 1) :=
        mul_le_mul_of_nonneg_right hs (by positivity)
    _ = v (β - 1) := one_mul _

private lemma val_prim_root {C : Type*} [Field C] (v : Valuation C NNReal) {p : ℕ}
    [hp : Fact p.Prime] {z : C} (hz : IsPrimitiveRoot z p) :
    v (z - 1) ^ (p - 1) = v (p : C) := by
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 := Polynomial.eval_one_cyclotomic_prime (R := C) (p := p)
  rw [hcyc, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rw [← h1, map_prod]
  have heq : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hp.out.pos).mp hμ
    rw [← Valuation.map_neg, neg_sub]
    exact le_antisymm (val_sub_one_le v hμ' hz) (val_sub_one_le v hz hμ')
  rw [Finset.prod_congr rfl heq, Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hp.out]

section Ainf

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

private lemma untilt_sub_one (x : PreTilt O p) :
    ∃ t : O, (x - 1).untilt = x.untilt - 1 + p * t := by
  have h1 := PreTilt.mk_untilt_eq_coeff_zero (x - 1)
  have h2 := PreTilt.mk_untilt_eq_coeff_zero x
  have h3 : Ideal.Quotient.mk (span {(p : O)}) ((x - 1).untilt - (x.untilt - 1)) = 0 := by
    rw [map_sub, h1, map_sub (Ideal.Quotient.mk _), map_one, h2, map_sub, map_one, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h3
  obtain ⟨t, ht⟩ := h3
  exact ⟨t, by linear_combination -ht⟩

private lemma val_untilt_sub_one (hv : v.Integers O) (x : PreTilt O p)
    (hlt : v (p : C) < v (algebraMap O C x.untilt - 1)) :
    v (algebraMap O C (x - 1).untilt) = v (algebraMap O C x.untilt - 1) := by
  obtain ⟨t, ht⟩ := untilt_sub_one x
  rw [ht, map_add, map_sub, map_one]
  have hpt : v (algebraMap O C ((p : O) * t)) ≤ v (p : C) := by
    rw [map_mul, map_natCast, map_mul]
    calc v (p : C) * v (algebraMap O C t) ≤ v (p : C) * 1 := mul_le_mul_of_nonneg_left (hv.map_le_one t) (by positivity)
      _ = v (p : C) := mul_one _
  exact Valuation.map_add_eq_of_lt_left v (lt_of_le_of_lt hpt hlt)

private lemma val_p_lt_one (hv : v.Integers O) : v (p : C) < 1 := by
  have h1 : v (p : C) ≤ 1 := by
    have h := hv.map_le_one (p : O)
    rwa [map_natCast] at h
  refine lt_of_le_of_ne h1 fun heq => ?_
  have hp0 : (p : C) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at heq
    exact zero_ne_one heq
  have hu := hv.isUnit_of_one (x := (p : O)) (by rw [map_natCast]; exact isUnit_iff_ne_zero.mpr hp0)
    (by rw [map_natCast]; exact heq)
  exact (Fact.out : ¬IsUnit (p : O)) hu

private lemma val_untilt_e_sub_one (hv : v.Integers O) (e : PreTilt O p)
    (hζ : IsPrimitiveRoot e.untilt p) :
    v (algebraMap O C (e - 1).untilt) ^ (p - 1) = v (p : C) := by
  have hpl : v (p : C) < 1 := val_p_lt_one hv
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n := by
    intro x n
    first
    | exact PreTilt.untilt_pow x n
    | exact map_pow _ x n
    | simp [PreTilt.untilt_pow]
  rcases hp.out.eq_two_or_odd' with h2 | hodd
  · subst h2
    set e' := (frobeniusEquiv (PreTilt O 2) 2).symm e with he'
    have hep : e' ^ 2 = e := by
      first
      | exact frobeniusEquiv_symm_pow_p 2 e
      | (have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O 2) 2 e
         rwa [frobenius_def] at h3)
      | simp [he']
    have hsub : (e' - 1) ^ 2 = e - 1 := by rw [sub_pow_char, one_pow, hep]
    have hm1 : e.untilt = -1 := hζ.eq_neg_one_of_two_right
    have h2ne : (2 : C) ≠ 0 := by
      intro h0
      apply hζ.ne_one (by norm_num)
      rw [hm1]
      have h5 : algebraMap O C (2 : O) = 0 := by rw [map_ofNat]; exact h0
      have h6 : (2 : O) = 0 := hv.hom_inj (h5.trans (map_zero _).symm)
      linear_combination -h6
    set z := algebraMap O C e'.untilt with hz
    have hz2 : z ^ 2 = -1 := by rw [hz, ← map_pow, ← hpow, hep, hm1, map_neg, map_one]
    have hvz : v z = 1 := by
      have h7 : v z ^ 2 = 1 := by rw [← map_pow, hz2, Valuation.map_neg, map_one]
      exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h7
    have hzz : (z - 1) ^ 2 = -2 * z := by linear_combination hz2
    have hx2 : v (z - 1) ^ 2 = v (2 : C) := by
      rw [← map_pow, hzz, map_mul, hvz, mul_one, Valuation.map_neg]
    have hx0 : v (z - 1) ≠ 0 := by
      intro h0
      rw [h0] at hx2
      exact ((Valuation.ne_zero_iff v).mpr h2ne) (by rw [← hx2]; simp)
    rw [Nat.cast_ofNat] at hpl
    have hxl : v (z - 1) < 1 := by
      by_contra hc
      push_neg at hc
      have h9 : 1 ≤ v (z - 1) ^ 2 := one_le_pow₀ hc
      rw [hx2] at h9
      exact absurd hpl (not_lt.mpr h9)
    have hlt : v ((2 : ℕ) : C) < v (algebraMap O C e'.untilt - 1) := by
      rw [Nat.cast_ofNat, ← hx2]
      first
      | exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl one_lt_two
      | exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl one_lt_two
    have hval := val_untilt_sub_one hv e' hlt
    rw [← hsub, hpow, map_pow, map_pow, hval, hx2]
    simp
  · have hx := val_prim_root v (hζ.map_of_injective hv.hom_inj)
    have hne : algebraMap O C e.untilt - 1 ≠ 0 := by
      intro h0
      apply hζ.ne_one hp.out.one_lt
      apply hv.hom_inj
      rw [map_one]
      exact sub_eq_zero.mp h0
    have hx0 : v (algebraMap O C e.untilt - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr hne
    have hxl : v (algebraMap O C e.untilt - 1) < 1 := by
      by_contra hc
      push_neg at hc
      have h9 : 1 ≤ v (algebraMap O C e.untilt - 1) ^ (p - 1) := one_le_pow₀ hc
      rw [hx] at h9
      exact absurd hpl (not_lt.mpr h9)
    have hp3 : 1 < p - 1 := by
      have h10 := hp.out.two_le
      obtain ⟨k, hk⟩ := hodd
      omega
    have hlt : v (p : C) < v (algebraMap O C e.untilt - 1) := by
      rw [← hx]
      first
      | exact pow_lt_self_of_lt_one₀ (pos_iff_ne_zero.mpr hx0) hxl hp3
      | exact pow_lt_self_of_lt_one (pos_iff_ne_zero.mpr hx0) hxl hp3
    rw [val_untilt_sub_one hv e hlt, hx]

end Ainf

theorem xiNu (p : ℕ) [hp : Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] (hK : KerThetaStatement p O) :
    XiNuStatement p C v O := by
  intro ε hv hζ
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  set e := (frobeniusEquiv (PreTilt O p) p).symm ε with he
  have hep : e ^ p = ε := by
    first
    | exact frobeniusEquiv_symm_pow_p p ε
    | (have h3 := frobenius_apply_frobeniusEquiv_symm (PreTilt O p) p ε
       rwa [frobenius_def] at h3)
    | simp [he]
  have hT : ∀ x : PreTilt O p, fontaineTheta O p (teichmuller p x) = x.untilt := by
    intro x
    first
    | exact fontaineTheta_teichmuller x
    | exact fontaineTheta_teichmuller O p x
    | simp [fontaineTheta]
  have h1 : teichmuller p ε - 1 =
      (∑ i ∈ Finset.range p, teichmuller p e ^ i) * (teichmuller p e - 1) := by
    rw [geom_sum_mul, ← map_pow, hep]
  have h2 : fontaineTheta O p (teichmuller p e - 1) = e.untilt - 1 := by
    rw [map_sub, map_one, hT]
  have hne : algebraMap O C (e.untilt - 1) ≠ 0 := by
    intro h0
    apply hζ.ne_one hp.out.one_lt
    have h4 := hv.hom_inj (h0.trans (map_zero _).symm)
    exact sub_eq_zero.mp h4
  have h3 : v (algebraMap O C (fontaineTheta O p (teichmuller p e - 1))) ^ (p - 1) = v (p : C) := by
    rw [h2, map_sub, map_one]
    exact val_prim_root v (hζ.map_of_injective hv.hom_inj)
  refine ⟨h1, h2, h3, fun pflat hpf => ?_⟩
  obtain ⟨hK1, -, -⟩ := hK pflat hpf
  have hvp : v (p : C) ≠ 0 := by
    rw [← h3, h2]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hne)
  have hxi : (∑ i ∈ Finset.range p, teichmuller p e ^ i) ∈ RingHom.ker (fontaineTheta O p) := by
    rw [RingHom.mem_ker, map_sum]
    simp only [map_pow, hT]
    exact hζ.geom_sum_eq_zero hp.out.one_lt
  rw [hK1] at hxi
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hxi
  have hmul : ∀ x y : PreTilt O p, (x * y).untilt = x.untilt * y.untilt := by
    intro x y
    first
    | exact PreTilt.untilt_mul x y
    | exact map_mul _ x y
    | simp [PreTilt.untilt_mul]
  have hpow : ∀ (x : PreTilt O p) (n : ℕ), (x ^ n).untilt = x.untilt ^ n := by
    intro x n
    first
    | exact PreTilt.untilt_pow x n
    | exact map_pow _ x n
    | simp [PreTilt.untilt_pow]
  have hone : (1 : PreTilt O p).untilt = 1 := by
    have h5 := hpow (1 : PreTilt O p) 0
    rwa [pow_zero, pow_zero] at h5
  have hct : ∀ x : PreTilt O p, WittVector.constantCoeff (teichmuller p x) = x := fun x =>
    WittVector.teichmuller_coeff_zero p x
  have hc := congrArg WittVector.constantCoeff ha
  rw [map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub, hct, map_sum] at hc
  simp only [map_pow, hct] at hc
  have hc2 : WittVector.constantCoeff a * ((-1) * pflat) = (e - 1) ^ (p - 1) := by
    rw [sub_one_pow_pred, ← hc]
    ring
  have hw := congrArg (fun x : PreTilt O p => v (algebraMap O C x.untilt)) hc2
  simp only [hmul, hpow, map_mul, map_pow] at hw
  rw [val_untilt_e_sub_one hv e hζ, hpf, map_natCast] at hw
  have hm1 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) = 1 := by
    have h5 : ((-1 : PreTilt O p).untilt) ^ 2 = 1 := by
      rw [← hpow, neg_one_sq, hone]
    have h6 : v (algebraMap O C ((-1 : PreTilt O p).untilt)) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, h5, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h6
  rw [hm1, one_mul] at hw
  have hX : v (algebraMap O C (WittVector.constantCoeff a).untilt) = 1 := by
    have h7 : v (algebraMap O C (WittVector.constantCoeff a).untilt) * v (p : C) = 1 * v (p : C) := by
      rw [one_mul]
      exact hw
    exact mul_right_cancel₀ hvp h7
  have hU : IsUnit (WittVector.constantCoeff a).untilt := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.mpr fun h0 => ?_) hX
    rw [h0, map_zero] at hX
    exact zero_ne_one hX
  have hunit : IsUnit a := by
    apply witt_isUnit
    apply perfection_isUnit
    have h8 := PreTilt.mk_untilt_eq_coeff_zero (WittVector.constantCoeff a)
    have h9 : IsUnit (PreTilt.coeff 0 (WittVector.constantCoeff a)) := by
      rw [← h8]
      exact hU.map _
    exact h9
  refine ⟨?_, hunit.unit, by rw [IsUnit.unit_spec, ha]⟩
  rw [hK1, ← ha, Ideal.span_singleton_mul_left_unit hunit]

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

private lemma frob_bij : Function.Bijective (WittVector.frobenius : WittVector p R → WittVector p R) := by
  constructor
  · intro x y h
    ext n
    have h' := congrArg (fun z => WittVector.coeff z n) h
    simp only [WittVector.coeff_frobenius_charP] at h'
    apply (frobeniusEquiv R p).injective
    rw [_root_.frobeniusEquiv_apply, _root_.frobeniusEquiv_apply, frobenius_def, frobenius_def]
    exact h'
  · intro x
    refine ⟨WittVector.mk p (fun n => (frobeniusEquiv R p).symm (x.coeff n)), ?_⟩
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have h := (frobeniusEquiv R p).apply_symm_apply (x.coeff n)
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h

lemma mem_span_p_iff (x : WittVector p R) : x ∈ span {(p : WittVector p R)} ↔ x.coeff 0 = 0 := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_zero]
  · intro hx
    obtain ⟨y, hy⟩ := (frob_bij (p := p) (R := R)).2 (WittVector.mk p (fun n => x.coeff (n + 1)))
    refine Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩
    rw [← WittVector.verschiebung_frobenius, hy]
    ext n
    cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, hx]
    | succ n => exact WittVector.verschiebung_coeff_succ _ n

lemma p_mul_eq_zero (x : WittVector p R) (h : x * p = 0) : x = 0 := by
  rw [← WittVector.verschiebung_frobenius] at h
  have h2 : WittVector.frobenius x = 0 := by
    ext n
    have h3 := congrArg (fun z => WittVector.coeff z n.succ) h
    simpa only [WittVector.verschiebung_coeff_succ, WittVector.zero_coeff] using h3
  apply (frob_bij (p := p) (R := R)).1
  rw [h2, map_zero]

lemma p_mem_nonZeroDivisors : (p : WittVector p R) ∈ nonZeroDivisors (WittVector p R) := mem_nonZeroDivisors_iff.mpr
  ⟨fun x hx => p_mul_eq_zero x (by rwa [mul_comm] at hx), fun x hx => p_mul_eq_zero x hx⟩

private lemma mul_root_eq_zero (w y : R) (h : w * y = 0) :
    w * (frobeniusEquiv R p).symm y = 0 := by
  have hr : ((frobeniusEquiv R p).symm y) ^ p = y := by
    have h1 := (frobeniusEquiv R p).apply_symm_apply y
    rwa [_root_.frobeniusEquiv_apply, frobenius_def] at h1
  have hz : (w * (frobeniusEquiv R p).symm y) ^ p = 0 := by
    rw [mul_pow, hr]
    calc w ^ p * y = w ^ (p - 1) * (w * y) := by
          rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      _ = 0 := by rw [h, mul_zero]
  apply (frobeniusEquiv R p).injective
  rw [map_zero, _root_.frobeniusEquiv_apply, frobenius_def, hz]

private lemma mul_iterate_root_eq_zero (w y : R) (h : w * y = 0) (n : ℕ) :
    w * ((frobeniusEquiv R p).symm^[n]) y = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mul_root_eq_zero w _ ih

end Witt

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type*} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

lemma pflat_mul_eq_zero (hO : ∀ x : O, (p : O) * x = 0 → x = 0) (pflat : PreTilt O p)
    (hpf : pflat.untilt = (p : O)) (x : PreTilt O p) (hx : pflat * x = 0) : x = 0 := by
  have hu0 : (0 : PreTilt O p).untilt = 0 := by
    have h1 : (0 : PreTilt O p).untilt = (p : O) * (0 : PreTilt O p).untilt := by
      rw [← hpf, ← map_mul, mul_zero]
    have hJ := IsAdicComplete.le_jacobson_bot (span {(p : O)}) (Ideal.mem_span_singleton_self (p : O))
    rw [Ideal.mem_jacobson_bot] at hJ
    have h2 : ((p : O) * -1 + 1) * (0 : PreTilt O p).untilt = 0 := by
      linear_combination h1
    exact ((hJ (-1)).mul_right_eq_zero).mp h2
  have hzero : ∀ y : PreTilt O p, pflat * y = 0 → PreTilt.coeff 0 y = 0 := by
    intro y hy
    have h1 : (p : O) * y.untilt = 0 := by rw [← hpf, ← map_mul, hy, hu0]
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hO _ h1, map_zero]
  have hred : ∀ n : ℕ, pflat * ((frobeniusEquiv (PreTilt O p) p).symm^[n]) x = 0 :=
    mul_iterate_root_eq_zero pflat x hx
  have hli : Function.LeftInverse (frobenius (PreTilt O p) p) (frobeniusEquiv (PreTilt O p) p).symm :=
    fun z => by rw [← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  apply Perfection.ext
  intro n
  have key := Perfection.coeff_iterate_frobenius (R := ModP O p) (p := p)
    ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) 0 n
  rw [zero_add] at key
  erw [hli.iterate n x] at key
  exact key.trans ((hzero _ (hred n)).trans (map_zero (Perfection.coeff (ModP O p) p n)).symm)

end Tilt

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem regular (hO : ∀ x : O, (p : O) * x = 0 → x = 0) : RegularStatement p O := by
  intro pflat hpf
  refine ⟨p_mem_nonZeroDivisors, ?_, ?_⟩
  · intro x hx
    rw [mem_span_p_iff] at hx ⊢
    rw [WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at hx
    exact pflat_mul_eq_zero hO pflat hpf _ hx
  · intro htop
    have h1 : (1 : WittVector p (PreTilt O p)) ∈
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp h1
    have h2 := congrArg (fun z => WittVector.coeff z 0) hce
    simp only [WittVector.add_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.teichmuller_coeff_zero, WittVector.one_coeff_zero] at h2
    have hp0 : (p : WittVector p (PreTilt O p)).coeff 0 = 0 := by
      rw [← mem_span_p_iff]; exact Ideal.mem_span_singleton_self _
    rw [hp0, mul_zero, zero_add, mul_comm] at h2
    have hu : IsUnit pflat := ⟨⟨pflat, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    have h3 := hu.map (PreTilt.untilt (O := O) (p := p))
    rw [hpf] at h3
    exact (Fact.out : ¬IsUnit (p : O)) h3

end Main

end ReciprocityTheory.PGsh
end
end

section
noncomputable section

open WittVector Ideal TensorProduct

namespace ReciprocityTheory.PGsh

section Principal

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

private lemma principal_inj (g : S)
    (h : ∀ m : M, g • m = 0 → (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m = 0) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul S M).comp (span {g}).subtype)) := by
  rw [injective_iff_map_eq_zero]
  have ex : ∀ t : span {g} ⊗[S] M,
      ∃ m : M, t = (⟨g, mem_span_singleton_self g⟩ : span {g}) ⊗ₜ[S] m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (tmul_zero _ _).symm⟩
    | tmul i m =>
      obtain ⟨i, hi⟩ := i
      obtain ⟨r, rfl⟩ := mem_span_singleton'.1 hi
      refine ⟨r • m, ?_⟩
      rw [← smul_tmul]
      congr 1
    | add x y hx hy =>
      obtain ⟨m₁, rfl⟩ := hx
      obtain ⟨m₂, rfl⟩ := hy
      exact ⟨m₁ + m₂, (tmul_add _ _ _).symm⟩
  intro t ht
  obtain ⟨m, rfl⟩ := ex t
  rw [lift.tmul] at ht
  exact h m ht

end Principal

section ZModSq

variable (p : ℕ) [hp : Fact p.Prime]

private lemma p_sq_zero : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma zmod_trichotomy (g : ZMod (p ^ 2)) :
    IsUnit g ∨ (∃ u : ZMod (p ^ 2), IsUnit u ∧ g = (p : ZMod (p ^ 2)) * u) ∨ g = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  have hg : g = ((g.val : ℕ) : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val g).symm
  have unit_of : ∀ k : ℕ, ¬ p ∣ k → IsUnit ((k : ℕ) : ZMod (p ^ 2)) := by
    intro k hk
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk))
  by_cases h1 : p ∣ g.val
  · obtain ⟨k, hk⟩ := h1
    by_cases h2 : p ∣ k
    · right; right
      obtain ⟨l, hl⟩ := h2
      rw [hg, hk, hl, Nat.cast_mul, Nat.cast_mul, ← mul_assoc, ← sq, p_sq_zero, zero_mul]
    · right; left
      exact ⟨k, unit_of k h2, by rw [hg, hk, Nat.cast_mul]⟩
  · left
    rw [hg]; exact unit_of _ h1

private lemma zmod_ideal (J : Ideal (ZMod (p ^ 2))) :
    J = span {0} ∨ J = span {(p : ZMod (p ^ 2))} ∨ J = span {1} := by
  by_cases hu : ∃ g ∈ J, IsUnit g
  · right; right
    obtain ⟨g, hgJ, hg⟩ := hu
    rw [span_singleton_one]
    exact eq_top_of_isUnit_mem J hgJ hg
  · by_cases hz : ∀ g ∈ J, g = 0
    · left
      rw [span_singleton_eq_bot.2 rfl]
      exact eq_bot_iff.2 (fun g hg => (mem_bot).2 (hz g hg))
    · right; left
      push Not at hz
      obtain ⟨g, hgJ, hg0⟩ := hz
      apply le_antisymm
      · intro x hx
        rcases zmod_trichotomy p x with h | ⟨u, _, rfl⟩ | rfl
        · exact absurd ⟨x, hx, h⟩ hu
        · exact mem_span_singleton'.2 ⟨u, mul_comm _ _⟩
        · exact zero_mem _
      · rw [span_singleton_le_iff_mem]
        rcases zmod_trichotomy p g with h | ⟨u, hu', rfl⟩ | rfl
        · exact absurd ⟨g, hgJ, h⟩ hu
        · have : (p : ZMod (p ^ 2)) = p * u * ↑hu'.unit⁻¹ := by
            rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
          rw [this]
          exact J.mul_mem_right _ hgJ
        · exact absurd rfl hg0

theorem flat_of_ann {M : Type*} [AddCommGroup M] [Module (ZMod (p ^ 2)) M]
    (h : ∀ m : M, (p : ZMod (p ^ 2)) • m = 0 → ∃ y : M, m = (p : ZMod (p ^ 2)) • y) :
    Module.Flat (ZMod (p ^ 2)) M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro J _
  rcases zmod_ideal p J with rfl | rfl | rfl
  · apply principal_inj
    intro m _
    have : (⟨0, mem_span_singleton_self 0⟩ : span {(0 : ZMod (p ^ 2))}) = 0 := rfl
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    obtain ⟨y, rfl⟩ := h m hm
    rw [← smul_tmul]
    have : (p : ZMod (p ^ 2)) • (⟨p, mem_span_singleton_self _⟩ : span {(p : ZMod (p ^ 2))}) = 0 := by
      apply Subtype.ext
      show (p : ZMod (p ^ 2)) * p = 0
      rw [← sq, p_sq_zero]
    rw [this, zero_tmul]
  · apply principal_inj
    intro m hm
    rw [one_smul] at hm
    rw [hm, tmul_zero]

end ZModSq

section Main

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem flatW' : FlatW'Statement p O := by
  intro pflat _
  set T : WittVector p (PreTilt O p) := teichmuller p pflat with hT
  set I : Ideal (WittVector p (PreTilt O p)) := span {(p : WittVector p (PreTilt O p)) ^ 2, T} with hI
  have hpc : ((p : ℕ) : WittVector p (PreTilt O p) ⧸ I) = Ideal.Quotient.mk I (p : WittVector p (PreTilt O p)) :=
    (map_natCast _ p).symm
  have hTI : Ideal.Quotient.mk I T = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (subset_span (by simp))
  have hann : ∀ x : WittVector p (PreTilt O p) ⧸ I, (p : WittVector p (PreTilt O p) ⧸ I) * x = 0 →
      ∃ y, x = (p : WittVector p (PreTilt O p) ⧸ I) * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hpc, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, mem_span_pair] at hx
    obtain ⟨c, d, hcd⟩ := hx
    have hd : d - teichmuller p (d.coeff 0) ∈ span {(p : WittVector p (PreTilt O p))} := by
      rw [mem_span_p_iff]
      have : constantCoeff (d - teichmuller p (d.coeff 0)) = 0 := by
        rw [map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, sub_self]
      exact this
    obtain ⟨e, he⟩ := mem_span_singleton'.1 hd
    have h1 : teichmuller p (d.coeff 0) * T = (a - c * p - e * T) * p := by
      have hd' : d = teichmuller p (d.coeff 0) + e * p := by rw [he]; ring
      rw [hd'] at hcd
      linear_combination hcd
    have h2 : teichmuller p (d.coeff 0) * T = 0 := by
      have hm : teichmuller p (d.coeff 0) * T ∈ span {(p : WittVector p (PreTilt O p))} :=
        mem_span_singleton'.2 ⟨_, h1.symm⟩
      rw [mem_span_p_iff, mul_coeff_zero, hT, teichmuller_coeff_zero, teichmuller_coeff_zero] at hm
      rw [hT, ← map_mul, hm, teichmuller_zero]
    have h3 : a = c * p + e * T := by
      have := p_mul_eq_zero _ (h1.symm.trans h2)
      linear_combination this
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [hpc, h3, map_add, map_mul, map_mul, hTI]
    ring
  refine ⟨?_, ?_, hann, ?_⟩
  · apply le_antisymm
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, 2 * p - T, by ring⟩, subset_span (by simp)⟩
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, T - 2 * p, by ring⟩, subset_span (by simp)⟩
  · rw [hpc, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_span (by simp)
  · intro _
    apply flat_of_ann
    intro m hm
    rw [Algebra.smul_def, map_natCast] at hm
    obtain ⟨y, hy⟩ := hann m hm
    exact ⟨y, by rw [Algebra.smul_def, map_natCast]; exact hy⟩

end Main

end ReciprocityTheory.PGsh
end
end

section
namespace ReciprocityTheory.PGsh

theorem a0 (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by
  intro C _ _ _ v O _ _ hv _ _
  have hK : KerThetaStatement p O := kerTheta (p := p) (C := C) (v := v) (O := O) hv
  have hO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    have h1 := congrArg (algebraMap O C) hx
    rw [map_mul, map_natCast, map_zero] at h1
    apply hv.hom_inj
    rw [map_zero]
    exact (mul_eq_zero.mp h1).resolve_left hp0
  obtain ⟨pf, hpf⟩ := exists_pflat (p := p) (hv := hv)
  exact ⟨⟨pf, hpf⟩, exists_eps (p := p) (hv := hv), hK,
    xiNu p C v O hK, regular (p := p) (O := O) (hO := hO), flatW' (p := p) (O := O)⟩

end ReciprocityTheory.PGsh
end
