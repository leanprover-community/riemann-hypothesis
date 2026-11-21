import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDedekind
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDualExp

section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem simple_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  obtain ⟨hA, -, h1, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have hac : (1 : Perm (Fin n))⁻¹ a < (1 : Perm (Fin n))⁻¹ c := by
    rw [inv_one, Perm.one_apply, Perm.one_apply, Fin.lt_def]; omega
  have := (hA a c h 1 hac).2.2
  rw [mul_one, invN.eq_def 1, h1, Finset.card_empty, zero_add] at this
  rw [(UpperTheory.V.AlgebraTools.hkOne R n q H b).1, this, pow_one]

private theorem symm_of_eigen {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H]
    [Algebra R H] (b : Bern n q H) (hb : b.Faithful) (y : MvPolynomial (Fin n) R)
    (hy : ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) * (b.th y * b.one) = q • (b.th y * b.one))
    (w : Perm (Fin n)) : rename w y = y := by
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y := by
    intro a c h
    have hac : a ≠ c := fun e => by rw [e] at h; omega
    obtain ⟨z, hz, e⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
    have e1 := hy a c h
    rw [← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc] at e1
    have e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0 := by
      apply hb
      rw [map_sub, map_add, map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, e1, sub_self]
    have e3 : (C q * X c - X a) * z = 0 := by
      simp only [smul_eq_C_mul, map_sub, map_one] at e2
      linear_combination e2 - C q * hz
    rcases mul_eq_zero.1 e3 with h0 | h0
    · have := congrArg (eval fun k => if k = a then (1 : R) else 0) h0
      simp [hac.symm] at this
    · rw [h0, mul_zero] at hz
      exact (sub_eq_zero.1 hz.symm).symm
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w
  · simp
  · intro a c h w _ ih
    rw [Perm.coe_mul, ← rename_rename, ih, hs a c h]

private theorem rename_rev_NN {R : Type} [CommRing R] (n : ℕ) (q : R) :
    rename (Fin.revPerm : Perm (Fin n)) (NN n q) = ∏ p ∈ pairs n, (X p.1 - C q * X p.2) := by
  rw [NN, map_prod]
  refine Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [pairs] using hp
  · intro p hp
    simpa [pairs] using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

private theorem rename_rev_De (R : Type) [CommRing R] (n : ℕ) :
    rename (Fin.revPerm : Perm (Fin n)) (De R n) = ∏ p ∈ pairs n, (X p.1 - X p.2) := by
  simpa [NN, De] using rename_rev_NN n (1 : R)

private theorem coeff_eq {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (F : Perm (Fin n) → K)
    (hF : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (∀ w : Perm (Fin n), rename w y = y) ∧
      algebraMap _ K y = ∑ u, F u * algebraMap _ K (rename u x))
    (N D : MvPolynomial (Fin n) R) (r : Perm (Fin n))
    (hr : F r = algebraMap _ K (rename r N) / algebraMap _ K (rename r D)) (v : Perm (Fin n)) :
    F v = algebraMap _ K (rename v N) / algebraMap _ K (rename v D) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, v = σ * r := ⟨v * r⁻¹, by simp⟩
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv
  have hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have h0 := UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by
    intro x
    obtain ⟨y, hy, e⟩ := hF x
    have e' := congrArg φ e
    rw [hφ, hy, e, map_sum] at e'
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e', sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_
    rw [map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])
  have h1 := congrFun h0 (σ * r)
  simp only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1
  rw [h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]

theorem UpperTheory.V.AlgebraTools.hkSandwich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ x : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th (dd (NN n q * x)) * b.one := by
  intro R _ _ n q H _ _ b hb x
  let K := FractionRing (MvPolynomial (Fin n) R)
  choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K
  obtain ⟨-, -, -, hrev, hlt⟩ := UpperTheory.V.AlgebraTools.hkInv n
  obtain ⟨hD, hsg, -⟩ := UpperTheory.V.AlgebraTools.hkDe R n
  have hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      b.one * b.th x * b.one = b.th y * b.one ∧
      algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x) := by
    intro x
    choose y hy hy' using fun w => hf w x
    refine ⟨∑ w, y w, ?_, ?_⟩
    · rw [map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]
      rfl
    · simp only [map_sum, hy', Finset.sum_mul]
      exact Finset.sum_comm
  have hF := coeff_eq (K := K) (fun u => ∑ w, f w u) (by
    intro x
    obtain ⟨y, hy, e⟩ := hsum x
    refine ⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩
    rw [← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])
    (NN n q) (De R n) Fin.revPerm (by
    rw [Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev,
      rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])
  obtain ⟨y, hy, e⟩ := hsum x
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  have hD' : algebraMap _ K (De R n) ≠ 0 := fun h => hD (hinj (by rw [h, map_zero]))
  have : y = dd (NN n q * x) := by
    apply mul_left_cancel₀ hD
    apply hinj
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu := hF u
    rw [hu, hsg, map_mul]
    rcases Int.units_eq_one_or (Perm.sign u) with h | h
    · rw [h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']
    · rw [h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul,
        mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']
  rw [hy, this]
end

section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem X_sub_ne {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (q : R) {i j : Fin n} (h : i ≠ j) :
    (X i - C q * X j : MvPolynomial (Fin n) R) ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h0
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul, Finsupp.single_left_inj, h, Ne.symm h] at this

theorem UpperTheory.V.AlgebraTools.hkFaith :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ c : Perm (Fin n) → MvPolynomial (Fin n) R,
      (∀ x : MvPolynomial (Fin n) R, (∑ u, b.th (c u) * b.T u) * b.th x * b.one = 0) → c = 0 := by
  classical
  intro R _ _ n q H _ _ b hfaith c hc
  let K := FractionRing (MvPolynomial (Fin n) R)
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  choose F hF1 hF2 hF3 using fun u => UpperTheory.V.AlgebraTools.hkAct R n q H b K u
  choose Y hY1 hY2 using hF1
  have key : ∀ x : MvPolynomial (Fin n) R,
      ∑ v, (∑ u, algebraMap (MvPolynomial (Fin n) R) K (c u) * F u v) *
        algebraMap (MvPolynomial (Fin n) R) K (rename v x) = 0 := by
    intro x
    have h1 : b.th (∑ u, c u * Y u x) * b.one = 0 := by
      calc b.th (∑ u, c u * Y u x) * b.one
          = ∑ u, b.th (c u) * (b.th (Y u x) * b.one) := by
            rw [map_sum, Finset.sum_mul]; simp [map_mul, mul_assoc]
        _ = ∑ u, b.th (c u) * (b.T u * b.th x * b.one) := by simp [hY1]
        _ = (∑ u, b.th (c u) * b.T u) * b.th x * b.one := by
            rw [Finset.sum_mul, Finset.sum_mul]; simp [mul_assoc]
        _ = 0 := hc x
    have h2 := congrArg (algebraMap (MvPolynomial (Fin n) R) K) (hfaith _ h1)
    rw [map_sum, map_zero] at h2
    simp_rw [map_mul, hY2, Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hD := UpperTheory.V.AlgebraTools.hkDedekind R n K _ key
  by_contra hne
  obtain ⟨w0, hw0⟩ : ∃ w, c w ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨w, hwS, hmax⟩ := (Finset.univ.filter (fun u => c u ≠ 0)).exists_max_image invN
    ⟨w0, by simp [hw0]⟩
  have hcw : c w ≠ 0 := by simpa using hwS
  have hw := congrFun hD w
  simp only [Pi.zero_apply] at hw
  rw [Finset.sum_eq_single w] at hw
  · apply mul_ne_zero _ _ hw
    · exact fun h => hcw (hinj (by rw [h, map_zero]))
    · rw [hF2 w]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hlt : p.1 < p.2 := by
        simp [invSet, pairs] at hp
        exact hp.1
      have hpne : p.1 ≠ p.2 := ne_of_lt hlt
      refine div_ne_zero ?_ ?_
      · exact fun h => X_sub_ne q hpne (hinj (by rw [h, map_zero]))
      · intro h
        apply X_sub_ne (1 : R) hpne
        apply hinj
        simpa using h
  · intro u _ hu
    by_cases hcu : c u = 0
    · simp [hcu]
    · rw [hF3 u w (fun h => hu h.symm) (hmax u (by simp [hcu])), mul_zero]
  · simp
end

section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSpan :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (w : Perm (Fin n)) (c : Perm (Fin n) → MvPolynomial (Fin n) R),
      ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, b.T w * ∑ u, b.th (c u) * b.T u = ∑ u, b.th (c' u) * b.T u := by
  intro R _ n q H _ _ b
  classical
  let S : Submodule R H :=
    { carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u}
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c₁, rfl⟩
        exact ⟨r • c₁, by simp [Finset.smul_sum]⟩ }
  have hone : ∀ x u, b.th x * b.T u ∈ S := by
    intro x u
    refine ⟨Pi.single u x, ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S := by
    intro a c hac x u
    by_cases hlt : u⁻¹ a < u⁻¹ c
    · rw [← b.T_mul a c hac u hlt]
      exact hone _ _
    · have hne : u⁻¹ c ≠ u⁻¹ a := by
        intro e
        have := (u⁻¹).injective e
        rw [this] at hac
        omega
      have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have e := b.T_mul a c hac _ hw'
      rw [swap_mul_self_mul] at e
      have e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u) := by
        calc b.T (swap a c) * b.T u = (b.T (swap a c) * b.T (swap a c)) * b.T (swap a c * u) := by
              rw [mul_assoc, ← e]
          _ = (q - 1) • b.T u + q • b.T (swap a c * u) := by
              rw [b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]
      rw [e2, mul_add, mul_smul_comm, mul_smul_comm]
      exact S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S := by
    rintro a c hac _ ⟨c₁, rfl⟩
    rw [Finset.mul_sum]
    refine S.sum_mem fun u _ => ?_
    obtain ⟨y, -, hy⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)
    rw [← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]
    exact S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))
  have key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · intro h hh
      rwa [b.T_one, one_mul]
    · intro a c hac w hw ih h hh
      rw [b.T_mul a c hac w hw, mul_assoc]
      exact hs a c hac _ (ih h hh)
  intro w c
  exact key w _ ⟨c, rfl⟩
end

section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSum :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) R), IsDual a c →
      ∑ i, b.th (a i) * b.one * b.th (c i) = b.th (NN n q) := by
  intro R _ _ n q H _ _ b hb ι _ a c hd
  classical
  let S : H → Prop := fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R,
    ∑ u, b.th (e u) * b.T u = h
  have S_zero : S 0 := ⟨0, by simp⟩
  have S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ + e₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [add_mul]
  have S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ - e₂, ?_⟩
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sub_mul]
  have S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k) :=
    fun s f hf => Finset.sum_induction f S S_add S_zero hf
  have S_th : ∀ x, S (b.th x) := by
    intro x
    refine ⟨fun u => if u = 1 then x else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Perm (Fin n))]
    · simp [b.T_one]
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have S_T : ∀ w h, S h → S (b.T w * h) := by
    rintro w h ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := UpperTheory.V.AlgebraTools.hkSpan R n q H b w e
    exact ⟨e', he'.symm⟩
  have S_thmul : ∀ x h, S h → S (b.th x * h) := by
    rintro x h ⟨e, rfl⟩
    refine ⟨fun u => x * e u, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, mul_assoc]
  have hE : S (∑ i, b.th (a i) * b.one * b.th (c i)) := by
    refine S_sum _ _ fun i _ => ?_
    rw [mul_assoc, Bern.one, Finset.sum_mul]
    exact S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))
  obtain ⟨e, he⟩ := S_sub _ _ hE (S_th (NN n q))
  have hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one
      = b.th (NN n q * x) * b.one := by
    intro x
    rw [Finset.sum_mul, Finset.sum_mul]
    have step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one
        = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
      intro i
      have hs := UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)
      calc b.th (a i) * b.one * b.th (c i) * b.th x * b.one
          = b.th (a i) * (b.one * b.th (c i * x) * b.one) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]
        _ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
            rw [map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum,
      (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]
  have he0 := UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by
    rw [he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])
  rw [he0] at he
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.mp he.symm)
end
