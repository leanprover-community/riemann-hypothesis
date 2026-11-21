import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HomUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)

theorem cc_logOf (G : FGLaw S d) (i : Fin d) : MvPowerSeries.constantCoeff (LogPf.logOf G i) = 0 := by
  have h0 : ∀ f : PS S 1 d, MvPowerSeries.constantCoeff f = f 0 := fun _ => rfl
  rw [h0]
  simp [LogPf.logOf, LogPf.prim]

theorem cc_pt' {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
  simp [pt]

theorem ev_eq_hom {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (f : PS S m d) : ev a f = MvPowerSeries.substAlgHom (hasSubst_pts a ha) f := by
  first
    | rfl
    | (rw [MvPowerSeries.coe_substAlgHom]; rfl)
    | simp [ev, MvPowerSeries.coe_substAlgHom]

theorem ev_at {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin m)
    (f : PS S 1 d) : ev a (ev ![pt S d j] f) = ev ![a j] f := by
  have h1 : ∀ (j' : Fin 1) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d j] : Fin 1 → Pt S m d) j' i) = 0 := by
    intro j' i; fin_cases j'; simp [pt]
  rw [ev_ev _ _ h1 ha]
  congr 1
  funext j' i
  fin_cases j'
  exact ev_X a ha j i

theorem ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) (a : Fin 2 → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    ev a (bilL G cc) = ∑ i, ∑ l, cc i l • (ev ![a 0] (LogPf.logOf G i) * ev ![a 1] (LogPf.logOf G l)) := by
  simp only [bilL, lg]
  rw [ev_eq_hom a ha]
  simp only [map_sum, map_smul, map_mul]
  simp only [← ev_eq_hom a ha]
  simp only [ev_at a ha]

private theorem ev_add_lemma {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (f g : PS S m d) : ev a (f + g) = ev a f + ev a g := by
  simp only [ev_eq_hom a ha, map_add]

theorem formal_log_add_last_two (G : FGLaw S d) (l : Fin d) :
    ev (n := 3) ![G.add (pt S d 1) (pt S d 2)] (LogPf.logOf G l) =
      ev (n := 3) ![pt S d 1] (LogPf.logOf G l) + ev (n := 3) ![pt S d 2] (LogPf.logOf G l) := by
  have hb : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i; fin_cases j <;> simp [pt]
  have hF : ∀ (j : Fin 1) (i : Fin d), MvPowerSeries.constantCoeff ((![G.F] : Fin 1 → Pt S 2 d) j i) = 0 := by
    intro j i; fin_cases j; simpa using G.const i
  have h := congrArg (ev (![pt S d 1, pt S d 2] : Fin 2 → Pt S 3 d)) (LogPf.logOf_add (G := G) l)
  rw [ev_ev _ _ hF hb, ev_add_lemma _ hb, ev_at _ hb, ev_at _ hb] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext j i
    fin_cases j
    rfl
  · rfl

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (f : PS S m d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pts a ha) (fun p => ha p.1 p.2) hf

theorem cc_bilL (G : FGLaw S d) (cc : Fin d → Fin d → S) : MvPowerSeries.constantCoeff (bilL G cc) = 0 := by
  have h1 : ∀ (j : Fin 2) (l : Fin d), MvPowerSeries.constantCoeff (lg G j l) = 0 := fun j l =>
    cc_ev_lemma (![pt S d j] : Fin 1 → Pt S 2 d) (fun j' k => by fin_cases j' <;> simp [pt]) _ (cc_logOf G l)
  simp only [bilL]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← smul_mul_assoc, map_mul, h1, mul_zero]

theorem constantCoeff_add_second_third (G : FGLaw S d) (i : Fin d) : MvPowerSeries.constantCoeff (G.add (pt S (n := 3) d 1) (pt S d 2) i) = 0 := by
  exact cc_ev_lemma (![pt S (n := 3) d 1, pt S d 2] : Fin 2 → Pt S 3 d) (fun j k => by fin_cases j <;> simp [pt]) (G.F i) (G.const i)

set_option maxHeartbeats 800000 in

theorem ev_expP {n : ℕ} (a : Fin 2 → Pt S n d) (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev a (expP (-bilL G cc)) = expP (-ev a (bilL G cc)) := by
  have h0 : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by
    rw [map_neg, cc_bilL, neg_zero]
  have h1 : ev a (-bilL G cc) = -ev a (bilL G cc) := by
    rw [ev_eq_hom a ha, ev_eq_hom a ha, map_neg]
  rw [← h1]
  have key := subst_exp (k := S) (σ := Fin 2 × Fin d) (τ := Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2) h0
  exact key

theorem twist_mul_second_argument (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (expP (-bilL G cc)) =
      ev (n := 3) ![pt S d 0, pt S d 1] (expP (-bilL G cc)) * ev (n := 3) ![pt S d 0, pt S d 2] (expP (-bilL G cc)) := by
  have ha : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, G.add (pt S d 1) (pt S d 2)] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i; fin_cases j
    · simp [pt]
    · simpa using constantCoeff_add_second_third G i
  have hb : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i; fin_cases j <;> simp [pt]
  have hc : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i; fin_cases j <;> simp [pt]
  have hsum : ev (![pt S d 0, G.add (pt S d 1) (pt S d 2)] : Fin 2 → Pt S 3 d) (bilL G cc) =
      ev (![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) (bilL G cc) + ev (![pt S d 0, pt S d 2] : Fin 2 → Pt S 3 d) (bilL G cc) := by
    rw [ev_bilL G cc _ ha, ev_bilL G cc _ hb, ev_bilL G cc _ hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [formal_log_add_last_two G l, mul_add, smul_add]
  rw [ev_expP _ ha, ev_expP _ hb, ev_expP _ hc, hsum, neg_add]
  exact exp_add (by rw [map_neg, cc_ev_lemma _ hb _ (cc_bilL G cc), neg_zero])
    (by rw [map_neg, cc_ev_lemma _ hc _ (cc_bilL G cc), neg_zero])

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (a : Fin n → Pt S n' d)
    (ha : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff (a p.1 p.2) = 0)
    (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ ha f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_X_psJet {n : ℕ} (m : ℕ) (q : Fin n × Fin d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n × Fin d) ^ (m + 1)) (X q) = psJet m (pt S d q.1 q.2) := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  have hc : ∀ e, MvPowerSeries.coeff e (pt S d q.1 q.2) = if e = Finsupp.single q 1 then (1 : S) else 0 := by
    intro e; simp [pt, MvPowerSeries.coeff_X]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [zero_add, pow_one]
    refine sub_mem (Ideal.subset_span ⟨q, rfl⟩) ?_
    unfold psTrunc
    refine Ideal.sum_mem _ fun e _ => ?_
    rw [hc]
    split_ifs with he
    · subst he
      exact Ideal.subset_span ⟨q, rfl⟩
    · rw [map_zero]
      exact Ideal.zero_mem _
  · have hmem : Finsupp.single q 1 ∈ degLE m := by
      unfold degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => if i = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = q
        · subst h
          simp
        · simp [h, Finsupp.single_apply, Ne.symm h]
      · rw [Finsupp.sum_single_index rfl]
        show 1 ≤ m
        omega
    have ht : psTrunc m (pt S d q.1 q.2) = X q := by
      unfold psTrunc
      rw [Finset.sum_eq_single (Finsupp.single q 1)]
      · rw [hc, if_pos rfl]
        rfl
      · intro b _ hb
        rw [hc, if_neg hb, map_zero]
      · intro h
        exact absurd hmem h
    rw [ht, sub_self]
    exact Ideal.zero_mem _

theorem mk_psIn_psJet {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m σ f) =
      psJet m (ev (fun i => pt S d (σ i)) f) := by
  have ha : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff ((fun i => pt S d (σ i)) p.1 p.2) = 0 := fun p => cc_pt' _ _
  have hφ : ∀ p : Fin n × Fin d, MvPolynomial.constantCoeff (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S) = 0 :=
    fun p => by simp
  have hmk : ∀ p : Fin n × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (X (σ p.1, p.2)) =
      psJet m ((fun i => pt S d (σ i)) p.1 p.2) := fun p => mk_X_psJet m (σ p.1, p.2)
  rw [← jetSubstP_psJet m (fun p : Fin n × Fin d => (X (σ p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (fun i => pt S d (σ i)) ha hφ hmk f]
  unfold jetSubstP jetMap liftJet psJet psIn
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
    AlgHom.coe_toRingHom, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  have hr : (aeval fun i : Fin n × Fin d => (X (σ i.1, i.2) : MvPolynomial (Fin n' × Fin d) S)) =
      rename (fun p : Fin n × Fin d => (σ p.1, p.2)) :=
    MvPolynomial.algHom_ext fun i => by simp
  erw [Ideal.Quotient.lift_mk]
  simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, hr, Ideal.Quotient.mkₐ_eq_mk]

theorem twist_mul_second_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by
  have hrel : (![pt S d 1, pt S d 2] : Fin 2 → Pt S 3 d) = fun i => pt S d ((![1, 2] : Fin 2 → Fin 3) i) := by
    funext i; fin_cases i <;> rfl
  have hφ3 : ∀ p : Fin 2 × Fin d, constantCoeff ((![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · simp
    · show constantCoeff (psIn d m ![1, 2] (G.F j)) = 0
      rw [FBIdPh.cc_psIn, G.const]
  have ha3 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt S d 0, G.add (pt S d 1) (pt S d 2)] : Fin 2 → Pt S 3 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i
    · exact cc_pt' _ j
    · exact constantCoeff_add_second_third G j
  rw [jetSubstP_psJet m _ (![pt S d 0, G.add (pt S d 1) (pt S d 2)] : Fin 2 → Pt S 3 d) ha3 hφ3
      (fun p => by
        obtain ⟨i, j⟩ := p
        fin_cases i
        · exact mk_X_psJet m _
        · show _ = psJet m (ev (n := 3) ![pt S d 1, pt S d 2] (G.F j))
          rw [hrel]
          exact mk_psIn_psJet m _ _),
    jetSubstP_psJet m _ (![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> exact cc_pt' _ j)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> simp)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> exact mk_X_psJet m _),
    jetSubstP_psJet m _ (![pt S d 0, pt S d 2] : Fin 2 → Pt S 3 d)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> exact cc_pt' _ j)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> simp)
      (fun p => by obtain ⟨i, j⟩ := p; fin_cases i <;> exact mk_X_psJet m _),
    twist_mul_second_argument, FBIdJet.psJet_mul]

theorem bal_sum {R : Type} [CommRing R] [Algebra S R] (cc M N : Matrix (Fin d) (Fin d) S)
    (hbal : Matrix.transpose M * cc = cc * N) (u v : Fin d → R) :
    ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) = ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) := by
  have key : ∀ a b, ∑ i, cc i b * M i a = ∑ l, cc a l * N l b := by
    intro a b
    have h := congrFun (congrFun hbal a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hL : ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) =
      ∑ a, ∑ b, (∑ i, cc i b * M i a) • (u a * v b) := by
    simp only [Finset.sum_mul, Finset.smul_sum, Finset.sum_smul, smul_mul_assoc, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_comm
  have hR : ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) =
      ∑ a, ∑ b, (∑ l, cc a l * N l b) • (u a * v b) := by
    simp only [Finset.mul_sum, Finset.smul_sum, Finset.sum_smul, mul_smul_comm, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [hL, hR]
  simp only [key]

abbrev lgv (G : FGLaw S d) : Pt S 1 d := fun i => LogPf.logOf G i

theorem dLin_lgv (G : FGLaw S d) : dLin (lgv G) = 1 := by
  refine Matrix.ext fun i j => ?_
  show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (LogPf.logOf G i) = (1 : Matrix (Fin d) (Fin d) S) i j
  have h := congrArg MvPowerSeries.constantCoeff (LogPf.pderiv_logOf G i j)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv, zero_add] at h
  have h2 := congrFun (congrFun (LogPf.cc_om G) i) j
  simp only [Matrix.map_apply] at h2
  simpa [h2] using h

private theorem ev_id_lemma_2 (G : FGLaw S d) (i : Fin d) : ev (n := 2) ![pt S d 0, pt S d 1] (G.F i) = G.F i := by
  have h01 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j <;> simp [pt]
  have h10 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j <;> simp [pt]
  conv_lhs => rw [← G.comm i]
  rw [ev_ev _ _ h10 h01]
  refine Eq.trans ?_ (G.comm i)
  congr 1
  funext j k
  fin_cases j
  · exact ev_X _ h01 1 k
  · exact ev_X _ h01 0 k

theorem add_lgv (G : FGLaw S d) :
    comp1 (lgv G) (G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1)) =
      comp1 (lgv G) (pt S (n := 2) d 0) + comp1 (lgv G) (pt S (n := 2) d 1) := by
  funext i
  have e : G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1) = G.F := by
    funext j; exact ev_id_lemma_2 G j
  rw [e]
  exact LogPf.logOf_add (G := G) i

theorem ev_lin {n : ℕ} (M : Matrix (Fin d) (Fin d) S) (u : Pt S n d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (i : Fin d) :
    ev ![u] (∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X ((0 : Fin 1), j) : PS S 1 d)) = ∑ j, M i j • u j := by
  have hu' : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![u] : Fin 1 → Pt S n d) j k) = 0 := by
    intro j k; fin_cases j; simpa using hu k
  rw [ev_eq_hom _ hu', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPowerSeries.smul_eq_C_mul, map_smul, ← ev_eq_hom _ hu', ev_X _ hu']
  rfl

theorem log_act {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (a : O) (i : Fin d) :
    comp1 (lgv B.G) (B.A.act a) i = ∑ j, dLin (B.A.act a) i j • lgv B.G j := by
  obtain ⟨ε, hinv, -⟩ := WickVanishing.formal_exp_law S d B.G (lgv B.G) (cc_logOf B.G) (dLin_lgv B.G) (add_lgv B.G)
  have hlin := WickVanishing.action_linear S d O B (lgv B.G) ε (cc_logOf B.G) (dLin_lgv B.G) (add_lgv B.G) hinv a
  have hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0 := hinv.1
  have hl0 : ∀ i, MvPowerSeries.constantCoeff (lgv B.G i) = 0 := cc_logOf B.G
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hAε : ∀ i, MvPowerSeries.constantCoeff (comp1 (B.A.act a) ε i) = 0 := WickVanishing.cc_comp1 _ _ hA0 hε0
  have e1 : comp1 (lgv B.G) (B.A.act a) = comp1 (comp1 (lgv B.G) (comp1 (B.A.act a) ε)) (lgv B.G) := by
    conv_lhs => rw [← WickVanishing.composition_identity_point_right (B.A.act a), ← hinv.2.2.1]
    rw [WickVanishing.germComp1_germComp1_eq_substitute _ _ _ hε0 hl0, WickVanishing.germComp1_germComp1_eq_substitute _ _ _ hAε hl0]
  rw [e1]
  show ev ![lgv B.G] (comp1 (lgv B.G) (comp1 (B.A.act a) ε) i) = _
  rw [hlin i, ev_lin _ _ hl0]

theorem ev_act_pt {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (a : O) {n : ℕ} (q : Fin n) (i : Fin d) :
    ev ![comp1 (B.A.act a) (pt S d q)] (LogPf.logOf B.G i) =
      ∑ j, dLin (B.A.act a) i j • ev ![pt S d q] (LogPf.logOf B.G j) := by
  have hq : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d q] : Fin 1 → Pt S n d) j k) = 0 := by
    intro j k; fin_cases j; simp [pt]
  have hA : ∀ (j : Fin 1) (k : Fin d), MvPowerSeries.constantCoeff ((![B.A.act a] : Fin 1 → Pt S 1 d) j k) = 0 := by
    intro j k; fin_cases j; simpa using B.A.const a k
  have e := ev_ev (![B.A.act a] : Fin 1 → Pt S 1 d) (![pt S d q] : Fin 1 → Pt S n d) hA hq (LogPf.logOf B.G i)
  have h2 : ev (![B.A.act a] : Fin 1 → Pt S 1 d) (LogPf.logOf B.G i) = ∑ j, dLin (B.A.act a) i j • lgv B.G j :=
    log_act B a i
  refine Eq.trans ?_ (e.symm.trans ?_)
  · congr 1
    funext j k
    fin_cases j
    rfl
  · rw [h2, ev_eq_hom _ hq, map_sum]
    simp only [map_smul]
    simp only [← ev_eq_hom _ hq]

theorem twist_bal {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (cc : Fin d → Fin d → S) (a b : O)
    (hbal : Matrix.transpose (dLin (B.A.act a)) * Matrix.of cc = Matrix.of cc * dLin (B.A.act b)) :
    ev (n := 2) ![comp1 (B.A.act a) (pt S d 0), pt S d 1] (expP (-bilL B.G cc)) =
      ev (n := 2) ![pt S d 0, comp1 (B.A.act b) (pt S d 1)] (expP (-bilL B.G cc)) := by
  have cA : ∀ (k : Fin d), MvPowerSeries.constantCoeff (comp1 (B.A.act a) (pt S (n := 2) d 0) k) = 0 := fun k =>
    cc_ev_lemma (![pt S d 0] : Fin 1 → Pt S 2 d) (fun j k' => by fin_cases j <;> simp [pt]) _ (B.A.const a k)
  have cB : ∀ (k : Fin d), MvPowerSeries.constantCoeff (comp1 (B.A.act b) (pt S (n := 2) d 1) k) = 0 := fun k =>
    cc_ev_lemma (![pt S d 1] : Fin 1 → Pt S 2 d) (fun j k' => by fin_cases j <;> simp [pt]) _ (B.A.const b k)
  have h0 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![comp1 (B.A.act a) (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · simpa using cA k
    · simp [pt]
  have h1 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, comp1 (B.A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · simp [pt]
    · simpa using cB k
  have key := bal_sum (R := PS S 2 d) (Matrix.of cc) (dLin (B.A.act a)) (dLin (B.A.act b)) hbal
    (fun k => ev (n := 2) ![pt S d 0] (LogPf.logOf B.G k)) (fun l => ev (n := 2) ![pt S d 1] (LogPf.logOf B.G l))
  simp only [Matrix.of_apply] at key
  rw [ev_expP _ h0, ev_expP _ h1, ev_bilL _ _ _ h0, ev_bilL _ _ _ h1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ev_act_pt]
  rw [key]

theorem twist_bal_jet {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (cc : Fin d → Fin d → S) (a b : O)
    (hbal : Matrix.transpose (dLin (B.A.act a)) * Matrix.of cc = Matrix.of cc * dLin (B.A.act b)) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL B.G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act b j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL B.G cc))) := by
  have hT : ∀ g : PS S 1 d, MvPowerSeries.constantCoeff g = 0 → MvPolynomial.constantCoeff (psTrunc m g) = 0 := by
    intro g hg
    unfold psTrunc
    rw [map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [MvPolynomial.constantCoeff_monomial]
    split_ifs with he
    · subst he; simpa using hg
    · rfl
  have h0 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![comp1 (B.A.act a) (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · exact cc_ev_lemma (![pt S d 0] : Fin 1 → Pt S 2 d) (fun j' k' => by fin_cases j' <;> simp [pt]) _ (B.A.const a k)
    · simp [pt]
  have h1 : ∀ (j : Fin 2) (k : Fin d), MvPowerSeries.constantCoeff ((![pt S d 0, comp1 (B.A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) j k) = 0 := by
    intro j k; fin_cases j
    · simp [pt]
    · exact cc_ev_lemma (![pt S d 1] : Fin 1 → Pt S 2 d) (fun j' k' => by fin_cases j' <;> simp [pt]) _ (B.A.const b k)
  have e0 : (fun i => pt S d ((![0] : Fin 1 → Fin 2) i)) = (![pt S d 0] : Fin 1 → Pt S 2 d) := by
    funext i; fin_cases i; rfl
  have e1 : (fun i => pt S d ((![1] : Fin 1 → Fin 2) i)) = (![pt S d 1] : Fin 1 → Pt S 2 d) := by
    funext i; fin_cases i; rfl
  have cA : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff ((![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j, k⟩; fin_cases j
    · show MvPolynomial.constantCoeff (psIn d m (![0] : Fin 1 → Fin 2) (B.A.act a k)) = 0
      unfold psIn
      rw [MvPolynomial.constantCoeff_rename]
      exact hT _ (B.A.const a k)
    · simp
  have cB : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff ((![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act b j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j, k⟩; fin_cases j
    · simp
    · show MvPolynomial.constantCoeff (psIn d m (![1] : Fin 1 → Fin 2) (B.A.act b k)) = 0
      unfold psIn
      rw [MvPolynomial.constantCoeff_rename]
      exact hT _ (B.A.const b k)
  have mA : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 2 × Fin d) ^ (m + 1))
      ((![fun j => psIn d m ![0] (B.A.act a j), fun j => X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) =
      psJet m ((![comp1 (B.A.act a) (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) p.1 p.2) := by
    rintro ⟨j, k⟩; fin_cases j
    · have h := mk_psIn_psJet m (![0] : Fin 1 → Fin 2) (B.A.act a k)
      rw [e0] at h
      exact h
    · exact mk_X_psJet m ((1 : Fin 2), k)
  have mB : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 2 × Fin d) ^ (m + 1))
      ((![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (B.A.act b j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) =
      psJet m ((![pt S d 0, comp1 (B.A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) p.1 p.2) := by
    rintro ⟨j, k⟩; fin_cases j
    · exact mk_X_psJet m ((0 : Fin 2), k)
    · have h := mk_psIn_psJet m (![1] : Fin 1 → Fin 2) (B.A.act b k)
      rw [e1] at h
      exact h
  rw [jetSubstP_psJet m _ (![comp1 (B.A.act a) (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) (fun p => h0 p.1 p.2) cA mA,
    jetSubstP_psJet m _ (![pt S d 0, comp1 (B.A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) (fun p => h1 p.1 p.2) cB mB,
    twist_bal B cc a b hbal]

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (d : ℕ)
variable (x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G)

theorem scaleGen_eq {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    scaleGen φ ε u g = scaleGenG Xo.univ.t φ ε u g := rfl

theorem mulGen_scale_right {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ Xo.univ.t.G.left)) (ε' : K' → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')) :
    LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g (scaleGenG Xo.univ.t φ' ε' v g') =
      scaleGenG Xo.univ.t _ _ v (LB.mulGen Xo.univ.t.PP.L φ ε φ' ε' g g') := by
  conv_lhs => rw [← FBIdLB.scaleGenG_one Xo.univ.t φ ε g]
  rw [FBIdLB.mulGen_scaleGenG, one_mul]

def tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) : FrTy y d x m :=
  scaleGen _ _ (unitΓ (T m)) (e m)

abbrev sub (m : ℕ) {n' : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S)
    (T : (Jet S (Fin 2 × Fin d) m)ˣ) : (Jet S (Fin n' × Fin d) m)ˣ :=
  Units.map (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2).toMonoidHom T

theorem pe_tw (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n' × Fin d) S) :
    pe y d x (tw y d x e T) m φ = scaleGenG Xo.univ.t _ _ (unitΓ (sub d m φ (T m))) (pe y d x e m φ) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
    (unitΓ (T m)) (e m) (homAt y.x (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  exact h1

theorem tw_zero (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (h0 : T 0 = 1) :
    tw y d x e T 0 = e 0 := by
  have h1 := FBIdLB.scaleGenG_one Xo.univ.t (cφ ![jpt y d x 0 (0 : Fin 2), jpt y d x 0 (1 : Fin 2)]) (cε 2) (e 0)
  have h2 : unitΓ (T 0) = 1 := by rw [h0, FBIdSy.unitΓ_one]
  show scaleGenG Xo.univ.t _ _ (unitΓ (T 0)) (e 0) = e 0
  rw [h2]
  exact h1

theorem tw_isGen (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ) (m : ℕ) (hg : (e m).IsGen) :
    (tw y d x e T m).IsGen := by
  intro i j
  have h := hg i j
  unfold tw scaleGen
  dsimp only
  erw [map_mul, map_mul, ReciprocityTheory.ChartRestriction.G.DVR.res_res', ReciprocityTheory.ChartRestriction.G.DVR.res_res', h]
  all_goals first | exact mul_left_comm _ _ _ | exact le_rfl

theorem isFrame_tw [StarRing (𝓞 E)] {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
    {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} (e : ∀ m, FrTy y d x m) (T : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hF : IsFrame y d x F act ph1 ph2 sy ad e)
    (hm1 : ∀ m, sub d m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub d m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub d m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)) :
    IsFrame y d x F act ph1 ph2 sy ad (tw y d x e T) := by
  refine ⟨fun m => tw_isGen y d x e T m (hF.gen m), fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hc⟩ := hF.ph1 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm1 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.ph2 m
    refine ⟨u, hu, ?_⟩
    rw [pe_tw, pe_tw, pe_tw, FBIdLB.invGen_scaleGenG, FBIdLB.invGen_scaleGenG, FBIdLB.mulGen_scaleGenG,
      FBIdLB.mulGen_scaleGenG, hm2 m, FBIdSy.unitΓ_mul, ← _root_.mul_inv, _root_.mul_inv_cancel, FBIdLB.scaleGenG_one]
    exact hc
  · obtain ⟨u, hu, hc⟩ := hF.sy m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc (unitΓ (T m))
    have eR : scaleGen _ _ (unitΓ u⁻¹) (pe y d x (tw y d x e T) m
        ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]) =
        scaleGenG Xo.univ.t _ _ (unitΓ (T m)) (scaleGen _ _ (unitΓ u⁻¹)
          (pe y d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)])) := by
      rw [pe_tw, hs m, scaleGen_eq, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG, FBIdSy.scaleGenG_scaleGenG,
        _root_.mul_comm]
    rw [eR]
    exact key
  · obtain ⟨wL, hwL, h⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hc⟩ := h m
    refine ⟨u, hu, ?_⟩
    have key := FBIdLB.corr_scaleGenG Xo.univ.t hc
      (unitΓ (sub d m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] (T m)))
    rw [pe_tw, pe_tw, hb m a, mulGen_scale_right, scaleGen_eq, FBIdSy.scaleGenG_scaleGenG,
      _root_.mul_comm, ← FBIdSy.scaleGenG_scaleGenG]
    exact key

theorem trunc_tw (e : ∀ m, FrTy y d x m) (T U : ∀ m, (Jet S (Fin 2 × Fin d) m)ˣ)
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (m : ℕ) :
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (tw y d x e T (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (tw y d x e T m) := by
  have h1 := FBIdLB.pullGen_scaleGenG Xo.univ.t
    (cφ ![jpt y d x (m + 1) (0 : Fin 2), jpt y d x (m + 1) (1 : Fin 2)]) (cε 2) (unitΓ (T (m + 1))) (e (m + 1))
    (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
  rw [FBIdLB.unitΓ_homAt] at h1
  have key := FBIdLB.corr_scaleGenG Xo.univ.t (hstep m)
    (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))))
  have hu : unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
      (T (m + 1))) * unitΓ (U m) = unitΓ (T m) := by
    rw [← FBIdSy.unitΓ_mul, hT m]
  have h2 : scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2)
      (unitΓ (Units.map (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m).toMonoidHom
        (T (m + 1)))) (scaleGenG Xo.univ.t _ _ (unitΓ (U m)) (e m)) = tw y d x e T m :=
    (FBIdSy.scaleGenG_scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)]) (cε 2) _ _
      (e m)).trans (congrArg (fun v => scaleGenG Xo.univ.t (cφ ![jpt y d x m (0 : Fin 2), jpt y d x m (1 : Fin 2)])
        (cε 2) v (e m)) hu)
  exact (congrArg₂ (LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _) h1 h2.symm).mpr key

theorem corr_refl {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε g g := by
  intro j j' _ _ hx
  have : j = j' := funext fun k => hx k k rfl
  subst this
  rfl

theorem fixTw_of [StarRing (𝓞 E)] [Algebra ℚ S] (C : ChartAt Xo c y) (T U : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ)
    (hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m))
    (hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m)
    (hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m))
    (hstep : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
        (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
      (scaleGen _ _ (unitΓ (U m)) (C.e m)))
    (hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m) (h0 : T 0 = 1) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ (T m)) (C.e m)) := by
  have hfr := isFrame_tw y C.d C.x C.e T C.frame hm1 hm2 hs hb
  have h0' := tw_zero y C.d C.x C.e T h0
  have hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
      (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act (tw y C.d C.x C.e T) C.wP 0)
        (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1) := by
    simp only [eL, pe]
    rw [h0']
    exact C.rig0
  refine ⟨tw y C.d C.x C.e T, hfr, hrig, fun m => trunc_tw y C.d C.x C.e T U hstep hT m, fun m => ?_⟩
  exact corr_refl _ _ _

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)

section Series

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

private lemma cc_pt_lemma {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]

private lemma cc_logOf_lemma_2 (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim _ 0 = 0
  simp [ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim]

private lemma germEval_oneStandardPoint_self_lemma_3 {n : ℕ} (b : Fin 2 → Pt S n d)
    (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (j : Fin 2) (f : PS S 1 d) :
    ev b (ev (n := 2) ![pt S d j] f) = ev ![b j] f := by
  rw [ev_ev _ _ (fun j' i => by fin_cases j'; exact cc_pt_lemma j i) hb]
  congr 1
  funext j' i
  fin_cases j'
  exact ev_X b hb j i

private lemma ev_hom_lemma_4 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a f = MvPowerSeries.substAlgHom (hasSubst_pts a ha) f := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

private lemma ev_neg_lemma_5 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a (-f) = -ev a f := by
  rw [ev_hom_lemma_4 a ha, ev_hom_lemma_4 a ha, map_neg]

private lemma eval_expSeries {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : ev a (expP f) = expP (ev a f) :=
  subst_exp (fun p : Fin m × Fin d => a p.1 p.2) (fun s => ha s.1 s.2) hf

private lemma cc_lg_lemma_7 {n : ℕ} (G : FGLaw S d) (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev (a := ![pt S d j])
    (fun j' i' => by fin_cases j'; exact cc_pt_lemma j i') (cc_logOf_lemma_2 G i)

private lemma cc_bilL_lemma_8 (G : FGLaw S d) (c : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (bilL G c) = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, MvPowerSeries.smul_eq_C_mul, cc_lg_lemma_7]

private lemma ev_bilL_lemma_9 {n : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S) (x y : Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → Pt S n d) j i) = 0) :
    ev ![x, y] (bilL G c) = ∑ i, ∑ l, c i l •
      (ev ![x] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) * ev ![y] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G l)) := by
  have key : ∀ f, ev ![x, y] f = MvPowerSeries.substAlgHom (hasSubst_pts _ ha) f :=
    fun f => ev_hom_lemma_4 _ ha f
  have hl : ∀ (j : Fin 2) i, ev ![x, y] (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) =
      ev ![(![x, y] : Fin 2 → Pt S n d) j] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) :=
    fun j i => germEval_oneStandardPoint_self_lemma_3 _ ha j _
  rw [key]
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_mul, ← key, ← key, hl, hl]
  all_goals rfl

theorem formal_log_add_first_two (G : FGLaw S d) (l : Fin d) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1)] (LogPf.logOf G l) =
      ev (n := 3) ![pt S d 0] (LogPf.logOf G l) + ev (n := 3) ![pt S d 1] (LogPf.logOf G l) := by
  have hb : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hF : ∀ j i, MvPowerSeries.constantCoeff ((![G.F] : Fin 1 → Pt S 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact G.const i
  have e1 : ev (n := 3) ![G.add (pt S d 0) (pt S d 1)] (LogPf.logOf G l) =
      ev ![pt S d 0, pt S d 1] (ev (n := 2) ![G.F] (LogPf.logOf G l)) := by
    rw [ev_ev _ _ hF hb]
    congr 1
    funext j i
    fin_cases j
    rfl
  rw [e1, ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf_add (G := G), ev_hom_lemma_4 _ hb, map_add,
    ← ev_hom_lemma_4 _ hb, ← ev_hom_lemma_4 _ hb, germEval_oneStandardPoint_self_lemma_3 _ hb, germEval_oneStandardPoint_self_lemma_3 _ hb]
  all_goals rfl

theorem constantCoeff_add_first_second (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (G.add (pt S (n := 3) d 0) (pt S d 1) i) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev (a := ![pt S d 0, pt S d 1]) (f := G.F i)
    (fun j i' => by fin_cases j <;> exact cc_pt_lemma _ i') (G.const i)

theorem twist_mul_first_argument (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (expP (-bilL G cc)) =
      ev (n := 3) ![pt S d 0, pt S d 2] (expP (-bilL G cc)) * ev (n := 3) ![pt S d 1, pt S d 2] (expP (-bilL G cc)) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff
      ((![G.add (pt S d 0) (pt S d 1), pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact constantCoeff_add_first_second G i
    · exact cc_pt_lemma _ i
  have h0 : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have h1 : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hB := cc_bilL_lemma_8 G cc
  have hneg : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by rw [map_neg, hB, neg_zero]
  have hsplit : ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G cc) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G cc) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G cc) := by
    rw [ev_bilL_lemma_9 G cc _ _ ha, ev_bilL_lemma_9 G cc _ _ h0, ev_bilL_lemma_9 G cc _ _ h1,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [formal_log_add_first_two G i, add_mul, smul_add]
  have c0 : MvPowerSeries.constantCoeff (-ev (n := 3) ![pt S d 0, pt S d 2] (bilL G cc)) = 0 := by
    rw [map_neg, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev _ h0 hB, neg_zero]
  have c1 : MvPowerSeries.constantCoeff (-ev (n := 3) ![pt S d 1, pt S d 2] (bilL G cc)) = 0 := by
    rw [map_neg, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev _ h1 hB, neg_zero]
  rw [eval_expSeries _ ha _ hneg, eval_expSeries _ h0 _ hneg, eval_expSeries _ h1 _ hneg,
    ev_neg_lemma_5 _ ha, ev_neg_lemma_5 _ h0, ev_neg_lemma_5 _ h1, hsplit, neg_add]
  exact exp_add c0 c1

theorem twist_sym (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (expP (-bilL G cc)) = expP (-bilL G cc) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hneg : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by
    rw [map_neg, cc_bilL_lemma_8 G cc, neg_zero]
  have hsw : ev (n := 2) ![pt S d 1, pt S d 0] (bilL G cc) = bilL G cc := by
    rw [ev_bilL_lemma_9 G cc _ _ ha]
    conv_rhs => rw [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hs l i, mul_comm] <;> rfl
  rw [eval_expSeries _ ha _ hneg, ev_neg_lemma_5 _ ha, hsw]

theorem bilL_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) : bilL G (c + c') = bilL G c + bilL G c' := by
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem bilL_zero (G : FGLaw S d) : bilL G 0 = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]

theorem twist_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) :
    expP (-bilL G (c + c')) = expP (-bilL G c) * expP (-bilL G c') := by
  rw [bilL_add, neg_add]
  exact exp_add (by rw [map_neg, cc_bilL_lemma_8, neg_zero]) (by rw [map_neg, cc_bilL_lemma_8, neg_zero])

theorem twist_zero (G : FGLaw S d) : expP (-bilL G 0) = 1 := by
  rw [bilL_zero, neg_zero]
  exact exp_zero

end Series

section Jet

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

private lemma mkX_lemma_10 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (s : ι) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S ι ^ (m + 1)) (MvPolynomial.X s) =
      psJet m (MvPowerSeries.X s : MvPowerSeries ι S) := by
  unfold Formalism.L2.Pj.psJet
  rw [Ideal.Quotient.eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_add, pow_one]
    refine Ideal.sub_mem _ (Ideal.subset_span ⟨s, rfl⟩) ?_
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_mem_orig 0 _ (MvPowerSeries.constantCoeff_X s)
  · have hmem : (Finsupp.single s 1 : ι →₀ ℕ) ∈ Formalism.L2.Pj.degLE m := by
      unfold Formalism.L2.Pj.degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => ⟨if i = s then 1 else 0, by split_ifs <;> omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = s
        · subst h
          simp
        · simp [h, Ne.symm h, Finsupp.single_apply]
      · rw [Finsupp.sum_single_index rfl]
        exact hm
    have htr : Formalism.L2.Pj.psTrunc m (MvPowerSeries.X s : MvPowerSeries ι S) = MvPolynomial.X s := by
      unfold Formalism.L2.Pj.psTrunc
      rw [Finset.sum_eq_single_of_mem _ hmem
        (fun b _ hb => by rw [MvPowerSeries.coeff_X, if_neg hb, map_zero])]
      rw [MvPowerSeries.coeff_X, if_pos rfl]
      rfl
    rw [htr, sub_self]
    exact Ideal.zero_mem _

private lemma jetSubstP_mk_eq_mk_aeval {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (Formalism.L2.Pj.orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S κ' ^ (m + 1))
        (MvPolynomial.aeval (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) P) :=
  rfl

private lemma ccOrig_lemma_12 {κ : Type} (P : MvPolynomial κ S) (hP : P ∈ Formalism.L2.Pj.orig S κ) :
    MvPolynomial.constantCoeff P = 0 := by
  have hle : Formalism.L2.Pj.orig S κ ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := κ) (R := S)) := by
    unfold Formalism.L2.Pj.orig
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp
  exact hle hP

private lemma mkIn_lemma_13 (G : FGLaw S d) (m : ℕ) (j : Fin d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1)) (psIn d m ![0, 1] (G.F j)) =
      psJet m (G.add (pt S (n := 3) d 0) (pt S d 1) j) := by
  have hcc : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact cc_pt_lemma _ i'
    · exact cc_pt_lemma _ i'
  have hX : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      (MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) : MvPolynomial (Fin 3 × Fin d) S) =
        psJet m ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  have e := jetSubstP_psJet (d := d) m
    (fun p : Fin 2 × Fin d => (MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) : MvPolynomial (Fin 3 × Fin d) S))
    (![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) hcc (fun p => MvPolynomial.constantCoeff_X S _) hX (G.F j)
  show _ = psJet m (ev (n := 3) ![pt S d 0, pt S d 1] (G.F j))
  rw [← e]
  unfold Formalism.L2.Pj.psJet Formalism.L2.Pj.psIn
  rw [jetSubstP_mk_eq_mk_aeval]
  congr 1
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero]
  have hr : (MvPolynomial.rename fun p : Fin 2 × Fin d => ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) :
      MvPolynomial (Fin 2 × Fin d) S →ₐ[S] MvPolynomial (Fin 3 × Fin d) S) =
      MvPolynomial.aeval fun i : Fin 2 × Fin d => MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) i.1, i.2) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.rename_X, MvPolynomial.aeval_X]
  rw [hr]

theorem twist_mul_first_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by
  have hcc : ∀ (x y : Pt S 3 d), (∀ i, MvPowerSeries.constantCoeff (x i) = 0) →
      (∀ i, MvPowerSeries.constantCoeff (y i) = 0) →
      ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → Pt S 3 d) p.1 p.2) = 0 := by
    intro x y hx hy
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact hx i'
    · exact hy i'
  have hpt : ∀ k : Fin 3, ∀ i, MvPowerSeries.constantCoeff ((pt S d k : Pt S 3 d) i) = 0 :=
    fun k i => cc_pt_lemma k i
  have hXc : ∀ (k k' : Fin 3), ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => X (k, j), fun j => X (k', j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) = 0 := by
    intro k k'
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact MvPolynomial.constantCoeff_X S _
    · exact MvPolynomial.constantCoeff_X S _
  have hXm : ∀ (k k' : Fin 3), ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      ((![fun j => X (k, j), fun j => X (k', j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) =
        psJet m ((![pt S d k, pt S d k'] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    intro k k'
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  have hφ : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · show MvPolynomial.constantCoeff (MvPolynomial.rename _ _) = 0
      rw [MvPolynomial.constantCoeff_rename]
      exact ccOrig_lemma_12 _ (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_mem_orig m _ (G.const i'))
    · exact MvPolynomial.constantCoeff_X S _
  have hmk : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      ((![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) =
        psJet m ((![G.add (pt S d 0) (pt S d 1), pt S d 2] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkIn_lemma_13 G m i'
    · exact mkX_lemma_10 m _
  have hA := hcc (G.add (pt S d 0) (pt S d 1)) (pt S d 2) (fun i => constantCoeff_add_first_second G i) (hpt 2)
  rw [jetSubstP_psJet m _ _ hA hφ hmk, jetSubstP_psJet m _ _ (hcc _ _ (hpt 0) (hpt 2)) (hXc 0 2) (hXm 0 2),
    jetSubstP_psJet m _ _ (hcc _ _ (hpt 1) (hpt 2)) (hXc 1 2) (hXm 1 2), twist_mul_first_argument G cc,
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul]

theorem twist_sym_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      psJet m (expP (-bilL G cc)) := by
  have hcc : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact cc_pt_lemma _ i'
    · exact cc_pt_lemma _ i'
  have hXc : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact MvPolynomial.constantCoeff_X S _
    · exact MvPolynomial.constantCoeff_X S _
  have hXm : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 2 × Fin d) ^ (m + 1))
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) =
        psJet m ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  rw [jetSubstP_psJet m _ _ hcc hXc hXm, twist_sym G cc hs]

def twU (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) : (Jet S (Fin 2 × Fin d) m)ˣ where
  val := psJet m (expP (-bilL G c))
  inv := psJet m (expP (-bilL G (-c)))
  val_inv := by rw [← FBIdJet.psJet_mul, ← twist_add, add_neg_cancel, twist_zero, FBIdJet.psJet_one]
  inv_val := by rw [← FBIdJet.psJet_mul, ← twist_add, neg_add_cancel, twist_zero, FBIdJet.psJet_one]

theorem twU_val (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) :
    (twU G c m : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL G c)) := rfl

end Jet

section Chart

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)

theorem fixTw [StarRing (𝓞 E)] (C : ChartAt Xo c y) (cc : ℕ → Fin C.d → Fin C.d → S) (h0 : cc 0 = 0)
    (hsym : ∀ m i j, cc m i j = cc m j i)
    (hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (cc m) =
      Matrix.of (cc m) * dLin (C.B.A.act (H.bar a)))
    (hstep : ∀ m, ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (U : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m - cc (m + 1)))) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen _ _ (unitΓ U) (C.e m))) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)) := by
  choose U hU hc using hstep
  let T : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ := fun m => twU C.B.G (cc m) m
  have hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_first_argument_jet C.B.G (cc m) m)
  have hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_second_argument_jet C.B.G (cc m) m)
  have hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m := fun m =>
    Units.ext (twist_sym_jet C.B.G (cc m) (hsym m) m)
  have hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m) :=
    fun m a => Units.ext (twist_bal_jet C.B (cc m) a (H.bar a) (hbal m a) m)
  have hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m := fun m => Units.ext (by
    rw [Units.val_mul, Units.coe_map, hU m]
    show (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)
      (psJet (m + 1) (expP (-bilL C.B.G (cc (m + 1))))) * _ = psJet m (expP (-bilL C.B.G (cc m)))
    rw [ExpGB.jetTrunc_psJet, ← FBIdJet.psJet_mul, ← twist_add, add_sub_cancel])
  have hT0 : T 0 = 1 := Units.ext (by
    show psJet 0 (expP (-bilL C.B.G (cc 0))) = 1
    rw [h0, twist_zero, FBIdJet.psJet_one])
  obtain ⟨e', hfr, hrig, htr, hcorr⟩ := fixTw_of y C T U hm1 hm2 hs hb hc hT hT0
  exact ⟨e', hfr, hrig, htr, fun m => ⟨T m, twU_val _ _ _, hcorr m⟩⟩

end Chart

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
end
end
