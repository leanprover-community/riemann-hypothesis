import ReciprocityTheory.Chebotarev.NZIdeal

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

def Smooth {E : Type} [Field E] [NumberField E] (S : Finset (Prm E)) (a : Ideal (𝓞 E)) : Prop :=
  ∀ q : Prm E, q.asIdeal ∣ a → q ∈ S

theorem prm_eq_of_dvd {E : Type} [Field E] [NumberField E] {p q : Prm E}
    (h : p.asIdeal ∣ q.asIdeal) : p = q :=
  IsDedekindDomain.HeightOneSpectrum.ext ((prime_dvd_prime_iff_eq p.prime q.prime).1 h)

theorem smooth_empty_iff {E : Type} [Field E] [NumberField E] {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) :
    Smooth ∅ a ↔ a = ⊤ := by
  constructor
  · intro hs
    by_contra htop
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal a htop
    have hMb : M ≠ ⊥ := fun h => ha (le_bot_iff.1 (h ▸ haM))
    let q : Prm E := ⟨M, hM.isPrime, hMb⟩
    exact absurd (hs q (Ideal.dvd_iff_le.2 haM)) (Finset.notMem_empty q)
  · rintro rfl q hq
    rw [← Ideal.one_eq_top] at hq
    exact absurd (isUnit_of_dvd_one hq) q.prime.not_isUnit

theorem smooth_insert_mul {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} {b : Ideal (𝓞 E)}
    (q : Prm E) (k : ℕ) (hb : Smooth S b) : Smooth (insert q S) (q.asIdeal ^ k * b) := by
  intro p hp
  rcases p.prime.dvd_or_dvd hp with h | h
  · exact Finset.mem_insert.2 (Or.inl (prm_eq_of_dvd (p.prime.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (hb p h)

theorem smooth_insert_decomp {E : Type} [Field E] [NumberField E] [DecidableEq (Prm E)] {S : Finset (Prm E)} (q : Prm E)
    {a : Ideal (𝓞 E)} (ha : a ≠ ⊥) (hs : Smooth (insert q S) a) :
    ∃ (k : ℕ) (b : Ideal (𝓞 E)), b ≠ ⊥ ∧ Smooth S b ∧ a = q.asIdeal ^ k * b := by
  obtain ⟨k, b, hqb, hab⟩ := WfDvdMonoid.max_power_factor (a₀ := a) ha q.irreducible
  refine ⟨k, b, ?_, ?_, hab⟩
  · rintro rfl
    exact ha (by rw [hab, Ideal.mul_bot])
  · intro p hp
    have hpa : p.asIdeal ∣ a := hab ▸ dvd_mul_of_dvd_right hp _
    rcases Finset.mem_insert.1 (hs p hpa) with h | h
    · exact absurd (h ▸ hp) hqb
    · exact h

theorem smooth_mul_inj {E : Type} [Field E] [NumberField E] {S : Finset (Prm E)} {q : Prm E} (hq : q ∉ S)
    {b b' : Ideal (𝓞 E)} (hb : Smooth S b) (hb' : Smooth S b') {k k' : ℕ}
    (h : q.asIdeal ^ k * b = q.asIdeal ^ k' * b') : k = k' ∧ b = b' := by
  have hq0 : q.asIdeal ≠ 0 := q.ne_bot
  have key : ∀ {c c' : Ideal (𝓞 E)} {m m' : ℕ}, Smooth S c → m < m' →
      q.asIdeal ^ m * c ≠ q.asIdeal ^ m' * c' := by
    intro c c' m m' hc hlt he
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [show q.asIdeal ^ (m + n + 1) * c' = q.asIdeal ^ m * (q.asIdeal ^ (n + 1) * c') by
      rw [← mul_assoc, ← pow_add, add_assoc]] at he
    have hc' := mul_left_cancel₀ (pow_ne_zero m hq0) he
    exact hq (hc q (hc' ▸ dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero n)) _))
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd h (key hb hlt)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k hq0) h⟩
  · exact absurd h.symm (key hb' hlt)

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem euler_fin_pow {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b) (a : Ideal (𝓞 E)) (k : ℕ) :
    f (a ^ k) = f a ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, hf1]
  | succ k ih => rw [pow_succ, hmul, ih, pow_succ]

theorem euler_finite {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1)
    (S : Finset (Prm E)) :
    HasSum (Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1)) (∏ q ∈ S, (1 - f q.asIdeal)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hT : (⊤ : Ideal (𝓞 E)) ≠ ⊥ := top_ne_bot
    have key : Set.indicator {a : NZIdeal E | Smooth ∅ a.1} (fun a => f a.1) =
        fun a => if a = ⟨⊤, hT⟩ then (1:ℂ) else 0 := by
      funext a
      by_cases h : a = ⟨⊤, hT⟩
      · subst h
        have hs : Smooth (∅ : Finset (Prm E)) (⊤ : Ideal (𝓞 E)) := (smooth_empty_iff hT).2 rfl
        rw [Set.indicator_of_mem (show (⟨⊤, hT⟩ : NZIdeal E) ∈ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_pos rfl]
        show f ⊤ = 1
        rw [← Ideal.one_eq_top, hf1]
      · have hs : ¬ Smooth (∅ : Finset (Prm E)) a.1 := by
          intro hs
          exact h (Subtype.ext ((smooth_empty_iff a.2).1 hs))
        rw [Set.indicator_of_notMem (show a ∉ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_neg h]
    rw [key]
    exact hasSum_ite_eq _ _
  | insert q S hq ih =>
    rw [Finset.prod_insert hq]
    rw [← hasSum_subtype_iff_indicator] at ih ⊢
    have hgeo : HasSum (fun k : ℕ => f q.asIdeal ^ k) (1 - f q.asIdeal)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hlt q)
    have hs1 : Summable (fun k : ℕ => ‖f q.asIdeal ^ k‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hlt q)
    have hs2 : Summable (fun b : {a : NZIdeal E | Smooth S a.1} => ‖f b.1.1‖) :=
      hsum.subtype _
    have hprod : HasSum (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1)
        ((1 - f q.asIdeal)⁻¹ * ∏ x ∈ S, (1 - f x.asIdeal)⁻¹) :=
      by
        have ih' : HasSum (fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) (∏ x ∈ S, (1 - f x.asIdeal)⁻¹) := ih
        have h3 : Summable (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1) :=
          summable_mul_of_summable_norm (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hs1 hs2
        exact HasSum.mul (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hgeo ih' h3
    have hne : ∀ (k : ℕ) (b : {a : NZIdeal E | Smooth S a.1}), q.asIdeal ^ k * b.1.1 ≠ ⊥ := by
      intro k b
      exact mul_ne_zero (pow_ne_zero _ q.ne_bot) b.1.2
    let e : ℕ × {a : NZIdeal E | Smooth S a.1} → {a : NZIdeal E | Smooth (insert q S) a.1} :=
      fun p => ⟨⟨q.asIdeal ^ p.1 * p.2.1.1, hne p.1 p.2⟩, smooth_insert_mul q p.1 p.2.2⟩
    have hbij : Function.Bijective e := by
      constructor
      · rintro ⟨k, b⟩ ⟨k', b'⟩ h
        have h' : q.asIdeal ^ k * b.1.1 = q.asIdeal ^ k' * b'.1.1 :=
          congrArg (fun x : {a : NZIdeal E | Smooth (insert q S) a.1} => x.1.1) h
        obtain ⟨h1, h2⟩ := smooth_mul_inj hq b.2 b'.2 h'
        subst h1
        have hb : b = b' := Subtype.ext (Subtype.ext h2)
        rw [hb]
      · rintro ⟨⟨a, ha⟩, hs⟩
        obtain ⟨k, b, hb, hbs, rfl⟩ := smooth_insert_decomp q ha hs
        exact ⟨(k, ⟨⟨b, hb⟩, hbs⟩), rfl⟩
    refine (Equiv.ofBijective e hbij).hasSum_iff.mp ?_
    convert hprod using 1
    funext p
    simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
    rw [hmul, euler_fin_pow f hf1 hmul]

end ReciprocityTheory.Cheb
end

section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem exists_smooth {E : Type} [Field E] [NumberField E] (a : NZIdeal E) : ∃ S : Finset (Prm E), Smooth S a.1 := by
  have hfin := Ideal.finite_factors (R := 𝓞 E) (I := a.1) a.2
  exact ⟨hfin.toFinset, fun q hq => hfin.mem_toFinset.mpr hq⟩

theorem Smooth.mono {E : Type} [Field E] [NumberField E] {S T : Finset (Prm E)} {a : Ideal (𝓞 E)}
    (h : Smooth S a) (hST : S ⊆ T) : Smooth T a := fun q hq => hST (h q hq)

theorem euler_hasProd {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹) (∑' a : NZIdeal E, f a.1) := by
  unfold HasProd
  simp only [SummationFilter.unconditional_filter]
  have key : (fun S : Finset (Prm E) => ∏ q ∈ S, (1 - f q.asIdeal)⁻¹) =
      fun S => ∑' a : NZIdeal E, Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1) a := by
    funext S
    exact (euler_finite f hf1 hmul hsum hlt S).tsum_eq.symm
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun a : NZIdeal E => ‖f a.1‖) hsum ?_ ?_
  · intro a
    obtain ⟨S0, hS0⟩ := exists_smooth a
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop S0] with S hS
    have : a ∈ {a : NZIdeal E | Smooth S a.1} := Smooth.mono hS0 hS
    rw [Set.indicator_of_mem this]
  · exact Eventually.of_forall fun S a => norm_indicator_le_norm_self _ _

theorem euler_exp_log {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal)) = ∑' a : NZIdeal E, f a.1 := by
  have hinj : Function.Injective (fun q : Prm E => (⟨q.asIdeal, q.ne_bot⟩ : NZIdeal E)) := by
    intro q q' h
    exact IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hs1 : Summable (fun q : Prm E => ‖f q.asIdeal‖) := by
    have h := hsum.comp_injective hinj
    exact h
  have hs2 : Summable (fun q : Prm E => -f q.asIdeal) := (Summable.of_norm hs1).neg
  have hs3 : Summable (fun q : Prm E => -Complex.log (1 - f q.asIdeal)) := by
    have := (Complex.summable_log_one_add_of_summable hs2).neg
    simp only [← sub_eq_add_neg] at this
    exact this
  have hP := hs3.hasSum.cexp
  have hne : ∀ q : Prm E, 1 - f q.asIdeal ≠ 0 := by
    intro q h
    have h1 : f q.asIdeal = 1 := (sub_eq_zero.mp h).symm
    have := hlt q
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have hP' : HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹)
      (Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal))) := by
    have e : (Complex.exp ∘ fun q : Prm E => -Complex.log (1 - f q.asIdeal)) =
        fun q : Prm E => (1 - f q.asIdeal)⁻¹ := by
      funext q
      rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne q)]
    rw [e] at hP
    exact hP
  exact hP'.unique (euler_hasProd f hf1 hmul hsum hlt)

end ReciprocityTheory.Cheb
end
