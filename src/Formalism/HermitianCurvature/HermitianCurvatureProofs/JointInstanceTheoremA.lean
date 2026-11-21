import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

namespace Formalism.FourierDecayAlt.P.Jx7

section frames

end frames

section sizes
open scoped nonZeroDivisors
lemma rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
  exact_mod_cast this

lemma idl_ne_zero (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h] at h1
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := by
    have := rd_pos E
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  simp at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos

lemma sqrt_idl (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (μ : ℤ)
    (hg : 0 < g) : √(FractionalIdeal.absNorm (S6.idl E g (-1) (-μ)) : ℝ) =
      (((g : ℝ) * S6.rd E ^ μ) ^ S6.deg E)⁻¹ := by
  rw [hN E g (-1) (-μ) hg, ← inv_pow]
  congr 1
  rw [zpow_neg, zpow_neg, zpow_one, mul_inv]

theorem t_BlockLattices : BlockLattices := by
  intro hL hI hN E _ _ _ hU g r b s hg
  obtain ⟨-, -, -, -, f5, -, -, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b 1) 1 hg
  obtain ⟨-, -, -, -, k5, -, k7, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b s) s hg
  refine ⟨fun l hl => f5 hl, fun l hl => k5 hl, fun l hl => k7 hl, idl_ne_zero hN E g _ _ hg,
    idl_ne_zero hN E g _ _ hg, ?_, ?_, ?_⟩
  · have := (hI E g r b ((s + 1 : ℕ) : ℤ)).1
    rw [this]; congr 2; push_cast; ring
  · unfold S6.dualIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4; unfold S6.nuBlock; ring
  · unfold S6.liftIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4

section Gl
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)

lemma supI_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.supI de de' T T' l w := by
  unfold Sz.Glob.supI
  apply Real.sSup_nonneg
  rintro x ⟨Y, -, rfl⟩
  show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y
  unfold Sz.Cfg.be Sz.Cfg.core
  positivity

lemma supremum_first_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.cutSupLong de de' T T' l w := by
  unfold Sz.Glob.cutSupLong
  apply Real.sSup_nonneg
  rintro x ⟨Y, -, rfl⟩
  show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y
  unfold Sz.Cfg.be Sz.Cfg.core
  positivity

noncomputable def sp (p : Prop) [Decidable p] (w : ι) : ℝ :=
  if p then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w

lemma sp_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ sp G de de' T T' l p w := by
  unfold sp; split_ifs
  · exact supremum_first_nonneg G de de' T T' l hg hka w
  · exact supI_nonneg G de de' T T' l hg hka w

lemma supA_mul (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    G.g ^ G.m * ((G.ka ^ (G.m - 1))⁻¹ * supA G de de' T T' l (decide p) w) = sp G de de' T T' l p w := by
  unfold supA sp
  simp only [decide_eq_true_eq]
  field_simp

lemma supA_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ supA G de de' T T' l (decide p) w := by
  have h := sp_nonneg G de de' T T' l hg.le hka.le p w
  rw [← supA_mul G de de' T T' l hg hka p w] at h
  have hc : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹ := by positivity
  rw [← mul_assoc] at h
  exact nonneg_of_mul_nonneg_right h hc

lemma N_nonneg : 0 ≤ G.N := by unfold Sz.Glob.N; positivity



lemma memS (hX : XIsLamOne) (b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s) (hbs : b + s ≤ G.r + 2) :
    (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) ∈
      G.thrSet C de de' T T' l := by
  refine ⟨b, hb, by omega, ?_⟩
  rcases Nat.eq_or_lt_of_le hs with h1 | h1
  · subst h1
    rcases Nat.eq_or_lt_of_le hb with h2 | h2
    · subst h2
      left
      refine ⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]; simp [sp]
    · right; left
      refine ⟨h2, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]
      have : b ≠ 1 := by omega
      simp [sp, this]
  · right; right; left
    refine ⟨s, h1, by omega, Finset.prod_congr rfl fun w _ => ?_⟩
    have : s ≠ 1 := by omega
    simp [sp, this]

lemma memP (b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ G.r + 1) :
    (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) ∈
      G.thrSet C de de' T T' l :=
  ⟨b, hb, hbs, Or.inr (Or.inr (Or.inr rfl))⟩

end Gl


end sizes

section sums
open scoped nonZeroDivisors
theorem t_MajIsProf : MajIsProf := by
  intro E W _ _ D e hP ρ l
  unfold TB.Data.maj prof
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Equiv.symm_apply_apply]
  rw [hP v l]

theorem t_BoxSumLattice : BoxSumLattice := by
  intro hB
  obtain ⟨C0, hC0⟩ := hB
  refine ⟨|C0| + 1, by have := abs_nonneg C0; linarith, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hf1 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hp : 0 < (K : ℝ) - 5 / 2 := by linarith
  refine ⟨fun l => Finset.prod_nonneg fun w _ =>
    le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (apply_nonneg w l)) K), ?_⟩
  intro S hS
  have hRHS : 0 ≤ ((|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
      Fintype.card (InfinitePlace E) := by positivity
  by_cases hx0 : ∃ w, x w = 0
  · obtain ⟨w0, hw0⟩ := hx0
    have h0 : ∀ l ∈ S, prof x K l = 0 := by
      intro l _
      unfold prof
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [hw0, zero_div, zero_pow (by omega)]; simp
    rw [Finset.sum_eq_zero h0]; exact hRHS
  · push Not at hx0
    have hxpos : ∀ w, 0 < x w := fun w => lt_of_le_of_ne (hx w) (Ne.symm (hx0 w))
    have hP : 0 < ∏ w, x w := Finset.prod_pos fun w _ => hxpos w
    have hNq : (0 : ℚ) < FractionalIdeal.absNorm aa :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa)
        (Ne.symm (by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]))
    have hN : 0 < √(FractionalIdeal.absNorm aa : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNq)
    have hq : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := div_pos hN hP
    obtain ⟨Θ₀, hΘ₀def⟩ : ∃ Θ₀ : ℝ, Θ₀ = (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w) ^
        (((Fintype.card (InfinitePlace E) : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
    have hΘ₀pos : 0 < Θ₀ := by rw [hΘ₀def]; exact Real.rpow_pos_of_pos hq _
    have hΘ₀f : Θ₀ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := by
      rw [hΘ₀def]; exact Real.rpow_inv_natCast_pow hq.le (ne_of_gt hf1)
    have hpw : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ₀ ^ Fintype.card (InfinitePlace E) := by
      rw [hΘ₀f, le_div_iff₀ hP]
      calc (Θ / a) ^ Fintype.card (InfinitePlace E) * ∏ w, x w
          ≤ (Θ / a) ^ Fintype.card (InfinitePlace E) *
              ((a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = √(FractionalIdeal.absNorm aa : ℝ) := by
            rw [← mul_assoc, ← mul_pow]
            have : Θ / a * (a / Θ) = 1 := by field_simp
            rw [this, one_pow, one_mul]
    have hle : Θ / a ≤ Θ₀ := le_of_pow_le_pow_left₀ (ne_of_gt hf1) hΘ₀pos.le hpw
    have h2 : 2 < Θ₀ := lt_of_lt_of_le (by rw [lt_div_iff₀ ha0]; linarith) hle
    have key := hC0 E aa haa x Θ₀ (K : ℝ) hxpos h2 hK3 hΘ₀f S
      (fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩)
    have hsum : ∑ l ∈ S, prof x K l = ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ (K : ℝ)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold prof
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Real.rpow_natCast]
    rw [hsum]
    refine key.trans ?_
    have hΘa : 0 < Θ / a := div_pos hΘ0 ha0
    have h3 : Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      calc Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ (Θ / a) ^ (-((K : ℝ) - 5 / 2)) :=
            (by
              rw [Real.rpow_neg hΘ₀pos.le, Real.rpow_neg hΘa.le]
              exact inv_anti₀ (Real.rpow_pos_of_pos hΘa _) (Real.rpow_le_rpow hΘa.le hle hp.le))
        _ = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
            rw [Real.div_rpow hΘ0.le ha0.le, Real.rpow_neg ha0.le, div_inv_eq_mul, mul_comm]
    have h4 : |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ≤
        (|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hΘ₀pos _), mul_assoc]
      exact mul_le_mul (by linarith) h3 (Real.rpow_pos_of_pos hΘ₀pos _).le
        (by have := abs_nonneg C0; linarith)
    calc (C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)
        ≤ |(C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)| := le_abs_self _
      _ = |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ^ Fintype.card (InfinitePlace E) := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h4 _

theorem t_LatticeSumsJoint : LatticeSumsJoint := by
  intro hB
  obtain ⟨C, hC1, hC⟩ := t_BoxSumLattice hB
  refine ⟨C, hC1, ?_⟩
  intro E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI
  have hcard : Fintype.card (InfinitePlace E) = D.f := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hpc : ∀ ρ : Fin D.f → ℝ, ∏ w, ρ (e.symm w) = ∏ v, ρ v := fun ρ => Equiv.prod_comp e.symm ρ
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  constructor
  · intro i hi1 hi2 L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.1 i hi1 hi2
    have h1 := hC E (aaD i) (D.Lad i) (fun w => D.szD i (e.symm w)) D.K Θ 1 h0 hsub
      (fun w => hnn _) hK le_rfl (by linarith) (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    refine h2.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.one_rpow, mul_one]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : 1 ≤ a ^ ((D.K : ℝ) - 5 / 2) := Real.one_le_rpow ha (by linarith)
    nlinarith
  · intro i s hs1 hsi hi hnot L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.2 (i - s + 1) s (by omega) hs1 (by omega)
      (by rintro ⟨hb, hs⟩; exact hnot ⟨by omega, hs⟩)
    have h1 := hC E (aaL (i - s + 1) s) (D.Lap (i - s + 1) s)
      (fun w => D.szL (i - s + 1) s (e.symm w)) D.K Θ a h0 hsub
      (fun w => hnn _) hK ha hΘ (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    exact h2

end sums

section positivity

end positivity

section main
open scoped ComplexOrder

theorem jn_nonneg {E W : Type} [Field E] (D : TB.Data E W) (jn : ℝ) (hG : D.GramPSD) (hE : D.EstE jn) :
    0 ≤ jn := by
  have hmem : D.emp ∈ D.Wb D.Ntop := by
    unfold TB.Data.Wb
    rw [Finset.mem_filter]
    exact ⟨D.emp_mem, by rw [D.cnt_emp]; exact Nat.zero_le _⟩
  have ht := hE D.emp hmem
  refine ge_of_tendsto ht ?_
  refine eventually_nhdsWithin_of_forall ?_
  intro ε hε
  have hp := hG ε hε 0 D.emp {([] : TB.Pt E)}
  unfold TB.PSDOn at hp
  have hd := hp.diag_nonneg (i := ⟨[], by simp⟩)
  have hre : 0 ≤ (D.gram ε 0 D.emp [] []).re := by
    have := (Complex.le_def.1 hd).1
    simpa using this
  rw [D.wt_emp, div_one]; exact hre






end main

section kernels
open scoped ComplexOrder ComplexConjugate Matrix
section psd
variable {α : Type} {F : Finset α}

theorem psd_congr {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : TB.PSDOn F k) :
    TB.PSDOn F k' := by
  unfold TB.PSDOn at *
  have : (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y := by
    ext x y; exact (h x x.2 y y.2).symm
  rw [this]; exact hk

theorem psd_zero : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by
  unfold TB.PSDOn; exact Matrix.PosSemidef.zero

theorem psd_add {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at *
  exact hk.add hk'

theorem psd_sum {ι : Type} (s : Finset ι) (k : ι → α → α → ℂ) (hk : ∀ i ∈ s, TB.PSDOn F (k i)) :
    TB.PSDOn F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have h1 := psd_add (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.sum_insert ha]
end psd

theorem t_ProductLemma (hS : SchurProduct) (hD : ProductDomination) : ProductLemma := by
  classical
  intro E α P _ _ S F hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh' hne
    simp only [prodSys] at hne ⊢
    rw [AddSubgroup.mem_iInf]
    intro p
    exact (hok p).1 t t' ht ht' h hh h' hh' (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ p) h0))
  · intro t ht
    exact hS α P F (fun p => (S p).N t t) (fun p => (hok p).2.1 t ht)
  · intro t t' htt h hh h' hh'
    simp only [prodSys] at htt ⊢
    rw [AddSubgroup.mem_iInf] at htt
    exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t t' (htt p) h hh h' hh')
  · intro t
    exact hS α P F (fun p => (S p).Th t) (fun p => (hok p).2.2.2.1 t)
  · intro t ht
    exact hD α P F (fun p => (S p).N t t) (fun p => (S p).Th t) (fun p => (hok p).2.1 t ht)
      (fun p => (hok p).2.2.2.2.1 t ht)
  · intro R hR
    simp only [prodSys] at hR ⊢

    let ρ : P → E → E := fun p t => ((t : E ⧸ (S p).L)).out
    have hρ : ∀ p t, t - ρ p t ∈ (S p).L := by
      intro p t
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h2 := (QuotientAddGroup.eq (s := (S p).L)).1 h1
      have : t - ρ p t = -ρ p t + t := by abel
      rw [this]; exact h2
    have hρeq : ∀ p t t', ρ p t - ρ p t' ∈ (S p).L → ρ p t = ρ p t' := by
      intro p t t' h
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = ((ρ p t' : E) : E ⧸ (S p).L) := by
        rw [QuotientAddGroup.eq]
        have : -ρ p t + ρ p t' = -(ρ p t - ρ p t') := by abel
        rw [this]; exact neg_mem h
      have h2 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h3 : ((ρ p t' : E) : E ⧸ (S p).L) = (t' : E ⧸ (S p).L) := Quotient.out_eq' _
      show ((t : E ⧸ (S p).L)).out = ((t' : E ⧸ (S p).L)).out
      rw [← h2, ← h3, h1]
    let T : P → Finset E := fun p => R.image (ρ p)
    let ι : E → (P → E) := fun t p => ρ p t
    have hιinj : Set.InjOn ι R := by
      intro t ht t' ht' h
      apply hR t ht t' ht'
      rw [AddSubgroup.mem_iInf]
      intro p
      have h1 : ρ p t = ρ p t' := congrFun h p
      have h2 := hρ p t
      have h3 := hρ p t'
      have : t - t' = (t - ρ p t) - (t' - ρ p t') := by rw [h1]; abel
      rw [this]; exact sub_mem h2 h3
    have hιmem : R.image ι ⊆ Fintype.piFinset T := by
      intro τ hτ
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hτ
      exact Fintype.mem_piFinset.2 (fun p => Finset.mem_image_of_mem _ ht)
    have hTinc : ∀ p, ∀ x ∈ T p, ∀ y ∈ T p, x - y ∈ (S p).L → x = y := by
      intro p x hx y hy hxy
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hy
      exact hρeq p t t' hxy

    have hA : TB.PSDOn F (fun h h' => ∏ p, (S p).B h h' - ∏ p, ∑ x ∈ T p, (S p).Th x h h') :=
      hD α P F (fun p h h' => ∑ x ∈ T p, (S p).Th x h h') (fun p => (S p).B)
        (fun p => psd_sum (T p) (fun x => (S p).Th x) (fun x _ => (hok p).2.2.2.1 x))
        (fun p => (hok p).2.2.2.2.2 (T p) (hTinc p))

    have hB : ∀ Q : Finset (P → E), TB.PSDOn F (fun h h' => ∑ τ ∈ Q, ∏ p, (S p).Th (τ p) h h') := by
      intro Q
      apply psd_sum Q (fun τ h h' => ∏ p, (S p).Th (τ p) h h')
      intro τ _
      exact hS α P F (fun p => (S p).Th (τ p)) (fun p => (hok p).2.2.2.1 (τ p))
    refine psd_congr ?_ (psd_add hA (hB (Fintype.piFinset T \ R.image ι)))
    intro h hh h' hh'
    have h1 : ∑ t ∈ R, ∏ p, (S p).Th t h h' = ∑ τ ∈ R.image ι, ∏ p, (S p).Th (τ p) h h' := by
      rw [Finset.sum_image hιinj]
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t (ρ p t) (hρ p t) h hh h' hh')
    have h2 : ∏ p, ∑ x ∈ T p, (S p).Th x h h' = ∑ τ ∈ Fintype.piFinset T, ∏ p, (S p).Th (τ p) h h' :=
      Finset.prod_univ_sum T (fun p x => (S p).Th x h h')
    have h3 := Finset.sum_sdiff (f := fun τ => ∏ p, (S p).Th (τ p) h h') hιmem
    rw [h1, h2, ← h3]
    ring

section schur
variable {α : Type} {F : Finset α}

theorem psd_mul {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'

theorem psd_one : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by
  unfold TB.PSDOn
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext x y; simp [Matrix.conjTranspose_apply]
  · intro x
    have : star x ⬝ᵥ (Matrix.of fun _ _ : F => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_sum, one_mul,
        Finset.sum_mul]
    rw [this]; exact star_mul_self_nonneg _

theorem psd_prod {P : Type} (s : Finset P) (k : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_one
  | insert a s ha ih =>
    have h1 := psd_mul (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.prod_insert ha]

theorem psd_prod_dom {P : Type} (s : Finset P) (k K : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p))
    (hd : ∀ p ∈ s, TB.PSDOn F (fun x y => K p x y - k p x y)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, K p x y - ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have hka := hk a (Finset.mem_insert_self a s)
    have hda := hd a (Finset.mem_insert_self a s)
    have hKa : TB.PSDOn F (K a) := psd_congr (fun x _ y _ => by ring) (psd_add hda hka)
    have h1 := psd_mul hKa (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)))
    have h2 := psd_mul hda (psd_prod s k (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ (psd_add h1 h2)
    intro x _ y _
    rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring
end schur

theorem t_SchurProduct : SchurProduct := by
  intro α P _ F k hk
  exact psd_prod univ k (fun p _ => hk p)

theorem t_ProductDomination : ProductDomination := by
  intro α P _ F k K hk hd
  exact psd_prod_dom univ k K (fun p _ => hk p) (fun p _ => hd p)

theorem t_ProductLemma' : ProductLemma := t_ProductLemma t_SchurProduct t_ProductDomination

theorem t_DiagScale : DiagScale := by
  intro α F k a hk
  have h1 : TB.PSDOn F (fun x y => (a x : ℂ) * (a y : ℂ)) := by
    unfold TB.PSDOn
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext x y; simp [Matrix.conjTranspose_apply, mul_comm]
    · intro x
      have : star x ⬝ᵥ (Matrix.of fun i j : F => (a i : ℂ) * (a j : ℂ)) *ᵥ x =
          star (∑ i : F, (a i : ℂ) * x i) * ∑ i : F, (a i : ℂ) * x i := by
        rw [star_sum, Finset.sum_mul_sum]
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        simp; ring
      rw [this]; exact star_mul_self_nonneg _
  exact psd_mul h1 hk

end kernels

end Formalism.FourierDecayAlt.P.Jx7

namespace Formalism.FourierDecayAlt.P




theorem schur_product : Formalism.FourierDecayAlt.J.SchurProduct := Jx7.t_SchurProduct

theorem product_domination : Formalism.FourierDecayAlt.J.ProductDomination := Jx7.t_ProductDomination

theorem diagonal_scaling : Formalism.FourierDecayAlt.J.DiagScale := Jx7.t_DiagScale

theorem product_lemma : Formalism.FourierDecayAlt.J.ProductLemma := Jx7.t_ProductLemma'

end Formalism.FourierDecayAlt.P
