import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSCCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnOperator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SigCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCMain
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdMemPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.G2Assumption
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0

theorem kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by
  funext l l'
  show (if s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0) =
    (if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0)
  by_cases hs : s l = true ∧ s l' = false
  · rw [if_pos hs]
    by_cases hc : c l = c l'
    · rw [if_pos ⟨hc, hs⟩]
    · rw [if_neg (fun h => hc h.1), hFU l l' (fun h => hc h.1), mul_zero]
  · rw [if_neg hs, if_neg (fun h => hs h.2)]

theorem rename_qsmul {ι τ : Type} (e : ι → τ) (q : ℚ) (X : MvPolynomial ι k) :
    MvPolynomial.rename e (q • X) = q • MvPolynomial.rename e X := by
  exact map_rat_smul (MvPolynomial.rename e) q X

theorem ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by
  classical
  have hb0 : ∀ l, ((fun l => ((0 : Fin d → k), φ l)) l).1 = 0 := fun l => rfl
  have haa : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (u l', 0) = 0 := by
    intro l l' _
    simp [betaH]
  have hab : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (0, φ l') = 0 :=
    fun l l' hs => hUF l l' (fun h => h.2 hs)
  have hw := ordNabla_wick hN2 hN3 B h m s (fun l => (u l, 0)) (fun l => (0, φ l)) hb0 haa hab Q g
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hw
  have hdeg : (MvPolynomial.rename (sideE s) Q).totalDegree = Q.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv (R := k) (sideE s) Q
  rw [hw, kapW_eq_kapH m c s u φ hFU, hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rename_qsmul, ← ordNabla_eq B h m s (fun l => (u l, 0)) ?_, ordNabla_u hN2]
  intro l l' _
  exact nablaL_comm hN2 B h m _ _ (by simp [betaH])

theorem ordNabla_value_expand (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d)
    (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι π : Type} [Fintype ι] [DecidableEq π] (c : ι → π)
    (s : ι → Bool) (u φ : ι → Fin d → k) (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g)) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        constantCoeff (DpolyOf (B.FK k) u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) g) := by
  rw [ordNabla_expand hN2 hN3 B h m c s u φ hUF hFU Q g, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact hV R d O k B h hax m ι u _ g

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

def Mf (mu : Fin n → MvPolynomial ι k →ₗ[k] k) (P : MvPolynomial (ι × Fin n) k) : k :=
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1)

variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)

theorem Mf_subset (P : MvPolynomial (ι × Fin n) k) (S : Finset (ι × Fin n →₀ ℕ)) (hS : P.support ⊆ S) :
    Mf mu P = ∑ mo ∈ S, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1) := by
  unfold Mf
  refine Finset.sum_subset hS (fun mo _ h => ?_)
  first
    | rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.mp h, zero_mul]

theorem Mf_add (P Q : MvPolynomial (ι × Fin n) k) : Mf mu (P + Q) = Mf mu P + Mf mu Q := by
  classical
  rw [Mf_subset mu (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    Mf_subset mu P _ Finset.subset_union_left, Mf_subset mu Q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_add, add_mul]

theorem Mf_smul (a : k) (P : MvPolynomial (ι × Fin n) k) : Mf mu (a • P) = a * Mf mu P := by
  rw [Mf_subset mu (a • P) P.support MvPolynomial.support_smul, Mf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem Mf_zero : Mf mu (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  simp [Mf]

theorem Mf_sum {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin n) k) :
    Mf mu (∑ a ∈ s, P a) = ∑ a ∈ s, Mf mu (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Mf_zero mu]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Mf_add, ih]

theorem Mf_monomial (mo : ι × Fin n →₀ ℕ) (a : k) :
    Mf mu (monomial mo a) = a * ∏ b, mu b (monomial (colM mo b) 1) := by
  classical
  rw [Mf_subset mu _ {mo} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def combine (f : Fin n → (ι →₀ ℕ)) : ι × Fin n →₀ ℕ :=
  ∑ b, Finsupp.mapDomain (fun l => (l, b)) (f b)

theorem combine_apply (f : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : combine f (l, b) = f b l := by
  classical
  unfold combine
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply (fun x y h => (Prod.mk.inj h).1) (f b) l
  · intro b' _ hb'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact hb' (Prod.mk.inj hl').2
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem colM_combine (f : Fin n → (ι →₀ ℕ)) (b : Fin n) : colM (combine f) b = f b := by
  ext l
  simp [colM, combine_apply]

theorem combine_colM (mo : ι × Fin n →₀ ℕ) : combine (colM mo) = mo := by
  ext ⟨l, b⟩
  rw [combine_apply]
  simp [colM]

theorem prod_monomial' {β : Type} (s : Finset β) (g : β → ι × Fin n →₀ ℕ) (a : β → k) :
    ∏ b ∈ s, monomial (g b) (a b) = monomial (∑ b ∈ s, g b) (∏ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, ih, MvPolynomial.monomial_mul, Finset.sum_insert hx, Finset.prod_insert hx]

theorem prodQ_monomial (f : Fin n → (ι →₀ ℕ)) (a : Fin n → k) :
    prodQ (fun b => monomial (f b) (a b)) = monomial (combine f) (∏ b, a b) := by
  unfold prodQ
  simp only [colE, MvPolynomial.rename_monomial]
  rw [prod_monomial']
  rfl

theorem Mf_prodQ (R : Fin n → MvPolynomial ι k) : Mf mu (prodQ R) = ∏ b, mu b (R b) := by
  classical
  have hR : ∀ b, colE b (R b) = ∑ α ∈ (R b).support, colE b (monomial α (coeff α (R b))) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
  have hmu : ∀ b, mu b (R b) = ∑ α ∈ (R b).support, coeff α (R b) * mu b (monomial α 1) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => by
      rw [show monomial α (coeff α (R b)) = coeff α (R b) • monomial α (1 : k) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [prodQ, Finset.prod_congr rfl (fun b _ => hR b), Finset.prod_univ_sum, Mf_sum,
    Finset.prod_congr rfl (fun b _ => hmu b), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp := prodQ_monomial x (fun b => coeff (x b) (R b))
  simp only [prodQ] at hp
  rw [hp, Mf_monomial, Finset.prod_mul_distrib]
  simp only [colM_combine]

theorem degree_colM (mo : ι × Fin n →₀ ℕ) : ∑ b, (colM mo b).degree = mo.degree := by
  classical
  have hd : ∀ {σ : Type} [Fintype σ] (m : σ →₀ ℕ), m.degree = ∑ i, m i := by
    intro σ _ m
    unfold Finsupp.degree
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  simp only [hd]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [colM]

theorem totalDegree_monomial_one_le (α : ι →₀ ℕ) : (monomial α (1 : k)).totalDegree ≤ α.degree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro s hs
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)]
  exact le_rfl

theorem iter_linear (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    ∀ x : MvPolynomial (ι × Fin n) k, (secondOrder k c)^[i] x = ((soL c) ^ i) x := by
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

theorem iter_zero' (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    (secondOrder k c)^[i] (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  rw [iter_linear]
  exact map_zero _

variable [Algebra ℚ k]

theorem colAlg (κ : ι → ι → k) (lam : Fin n → (ι →₀ ℕ) → k)
    (hlm : ∀ b α, lam b α = ∑ i ∈ Finset.range ((monomial α (1 : k)).totalDegree + 1),
        mu b (((i.factorial : ℚ)⁻¹) • (secondOrder k κ)^[i] (monomial α 1)))
    (P : MvPolynomial (ι × Fin n) k)
    (hP : secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0) P = 0) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, lam b (colM mo b) = Mf mu P := by
  classical
  set N := P.totalDegree with hN
  set cc : ι × Fin n → ι × Fin n → k := cS κ (Finset.univ : Finset (Fin n)) with hcc
  have hccu : cc = fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0 := cS_univ κ
  have hE : ∀ b α, (monomial α (1 : k)).totalDegree ≤ N →
      lam b α = mu b (E1 κ 1 N (monomial α 1)) := by
    intro b α hα
    rw [hlm, E1, map_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hα)) (fun i hi hi' => ?_) |>.trans ?_
    · rw [so_iter_eq_zero κ i _ (by simp only [Finset.mem_range] at hi'; omega), smul_zero, map_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, ← algebraMap_smul k ((i.factorial : ℚ)⁻¹)]
  have hmo : ∀ mo ∈ P.support, ∏ b, lam b (colM mo b) =
      ∑ i ∈ Finset.range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
        Mf mu ((secondOrder k cc)^[i] (monomial mo 1)) := by
    intro mo hmo
    have hdeg : mo.degree ≤ N := by
      have := le_totalDegree hmo
      exact le_of_eq_of_le (by rfl) this
    have hD : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ (colM mo b).degree :=
      fun b => totalDegree_monomial_one_le _
    have hsum : ∑ b, (colM mo b).degree ≤ N := (degree_colM mo).le.trans hdeg
    have hb : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (hD b).trans ((Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ b)).trans hsum)
    rw [Finset.prod_congr rfl (fun b _ => hE b (colM mo b) (hb b)), ← Mf_prodQ]
    have hx := exp_cols κ 1 N (fun b => (colM mo b).degree) hsum Finset.univ
      (fun b => monomial (colM mo b) 1) hD
    simp only [Finset.mem_univ, if_true] at hx
    rw [← hx, prodQ_monomial, Finset.prod_const_one, combine_colM,
      exp_opA_apply _ _ _ _ ((totalDegree_monomial_one_le mo).trans hdeg), Mf_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mf_smul]
  rw [Finset.sum_congr rfl fun mo hmo' => by rw [hmo mo hmo']]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlin : ∀ i, ∑ mo ∈ P.support, P.coeff mo * ((algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
      Mf mu ((secondOrder k cc)^[i] (monomial mo 1))) =
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) * Mf mu ((secondOrder k cc)^[i] P) := by
    intro i
    conv_rhs => rw [as_sum P]
    rw [iter_linear, map_sum, Mf_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun mo _ => ?_
    rw [show monomial mo (P.coeff mo) = P.coeff mo • monomial mo (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Mf_smul, ← iter_linear]
    ring
  rw [Finset.sum_congr rfl fun i _ => hlin i, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [Function.iterate_succ_apply, hccu, hP, iter_zero', Mf_zero, mul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def valL {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (g : PS k 1 d) :
    MvPolynomial ι k →ₗ[k] k where
  toFun Q := MvPowerSeries.constantCoeff (DpolyOf (B.FK k) u Q g)
  map_add' P Q := by rw [GE.dpolyOf_add_P, map_add]
  map_smul' a Q := by
    rw [GE.dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C, RingHom.id_apply, smul_eq_mul]

theorem lemmaHCols_of (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : LemmaHColsSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι π _ _ c s u φ _ hUF hFU n P hP g
  have hP' : secondOrder k (fun p q : ι × Fin n =>
      if p.2 = q.2 then SCPf.kapH m c s u φ p.1 q.1 else 0) P = 0 := by
    rw [← hP]
    congr 1
    funext p q
    unfold SCPf.kapH
    by_cases h1 : p.2 = q.2
    · simp [h1]
    · simp [h1]
  have key := colAlg (fun b => valL B u (g b)) (SCPf.kapH m c s u φ)
    (fun b α => MvPowerSeries.constantCoeff (ordNabla k B h m s (fun l => (u l, φ l))
      (MvPolynomial.monomial α 1) (liftX k (g b))))
    (fun b α => SCPf.ordNabla_value_expand hV hN2 hN3 B h hax m c s u φ hUF hFU _ (g b)) P hP'
  exact key

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Lift

variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}

theorem liftX_one : liftX k (1 : PS k 1 d) = 1 := by
  rw [liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_one]

theorem liftX_add (f g : PS k 1 d) : liftX k (f + g) = liftX k f + liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_add]

theorem liftX_sub (f g : PS k 1 d) : liftX k (f - g) = liftX k f - liftX k g := by
  rw [liftX, liftX, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), map_sub]

theorem liftX_C (a : k) : liftX k (C a : PS k 1 d) = C a := by
  have h1 : (C a : PS k 1 d) = algebraMap k (PS k 1 d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h2 : (C a : AA k d) = algebraMap k (AA k d) a := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h1, h2, liftX, ← MvPowerSeries.coe_substAlgHom (liftX_hs k), AlgHom.commutes]

end Lift

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ig_FK (B : FB R d O) (j : Fin d) : B.FK k j ∈ Ig R k (Fin 2 × Fin d) := by
  simp only [FB.FK, FGLaw.mapF]
  exact ig_map _

theorem exp_conj_connection_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (w0 : O) (hw : w0 + star w0 = 1)
    (m : ℕ) (u' φ' : Fin d → R) (G : AA k d) (hG : G ∈ Ig R k (Fin d ⊕ Fin d)) :
    liftX k (FB.expS k (-((m : k) • B.hL k h w0))) *
      nabla k B h m (fun i => algebraMap R k (u' i))
        (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i)
        (liftX k (FB.expS k ((m : k) • B.hL k h w0)) * G) ∈ Ig R k (Fin d ⊕ Fin d) := by
  have cPA : CZ (![pt k (n := 1) d 0, B.actK k w0] : Fin 2 → Pt k 1 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (const_actK' B w0) CZ.nil)
  have ccf : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [nt_const_smul, hL_eq, cc_ev' cPA, cc_h hc, mul_zero]
  have ccf' : constantCoeff (-((m : k) • B.hL k h w0)) = 0 := by rw [map_neg, ccf, neg_zero]
  have hinv : liftX k (FB.expS k (-((m : k) • B.hL k h w0))) * liftX k (FB.expS k ((m : k) • B.hL k h w0)) = 1 := by
    rw [← liftX_mul, ← gt_expS_add _ _ ccf' ccf, neg_add_cancel, nt_expS_zero, liftX_one]
  rw [nabla_eq, vf_mul, vf_cf_liftX, dof_expS _ _ ccf, liftX_mul]
  have e : ∀ (a b x y z : AA k d), a * (b * x * G + b * y - z * (b * G)) = (a * b) * (x * G + y - z * G) :=
    fun a b x y z => by ring
  rw [e, hinv, one_mul, smul_eq_C_mul, dof_Cmul, liftX_mul, liftX_C]
  have hfm : fm k h (fun i => algebraMap R k (u' i)) =
      ∑ i, X (Sum.inr i) * C (algebraMap R k (u' i)) - liftX k (∑ i, sgOf k h i * C (algebraMap R k (u' i))) := by
    simp only [fm, sub_mul, Finset.sum_sub_distrib, liftX_sum, liftX_mul, liftX_C]
  rw [hfm]
  have e2 : ∀ (cm D S XC y : AA k d), cm * D * G + y - cm * (XC - S) * G = y + cm * (D + S - XC) * G :=
    fun cm D S XC y => by ring
  rw [e2, ← liftX_add]
  have hm : (C ((m : ℕ) : k) : AA k d) ∈ Ig R k (Fin d ⊕ Fin d) := by
    rw [← map_natCast (algebraMap R k) m]
    exact ig_C _
  refine add_mem ?_ (mul_mem (mul_mem hm (sub_mem (ig_liftX (rel_hL hc w0 hw _ fun j => ⟨u' j, rfl⟩)) ?_)) hG)
  · simp only [vf]
    refine sum_mem fun t _ => mul_mem ?_ (ig_pderiv hG t)
    rcases t with j | i
    · rw [cf_inl]
      exact ig_liftX (sum_mem fun i _ => mul_mem (ig_C _) (ig_ev cz1 integral_family_point_zero (ig_pderiv (ig_FK B j) _)))
    · have e3 : cf k B h (fun i => algebraMap R k (u' i))
          (fun i => algebraMap R k (φ' i) - (sg1 k h).mulVec (fun j => algebraMap R k (u' j)) i) (Sum.inr i) =
          liftX k (Dof (B.FK k) (fun j => algebraMap R k (u' j)) (sgOf k h i) -
            C (∑ j, sg1 k h i j * algebraMap R k (u' j))) + C (algebraMap R k (φ' i)) := by
        rw [cf_inr, liftX_sub, liftX_C]
        simp only [Matrix.mulVec, dotProduct, map_sub]
        ring
      rw [e3]
      exact add_mem (ig_liftX (dof_sig hc u' i)) (ig_C _)
  · exact sum_mem fun i _ => mul_mem (ig_X _) (ig_C _)

theorem connection_first_identity : ConnectionIntegrality := by
  intro R _ d O _ _ k _ _ _ _ B h hc w0 hw m ξ hξ G hG
  obtain ⟨u, φ, rfl⟩ := hξ
  have hI : ∀ Y : AA k d, Y ∈ Ig R k (Fin d ⊕ Fin d) → IntAA (R := R) k Y := by
    rintro Y ⟨g, rfl⟩ n
    exact ⟨MvPowerSeries.coeff n g, by rw [MvPowerSeries.coeff_map]⟩
  exact hI _ (exp_conj_connection_integral hc w0 hw m u φ G (ig_of_intAA hG))

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

theorem prod_mem_pow {R k : Type} [CommRing R] [CommRing k] [Algebra R k] (J : Submodule R k) {β : Type}
    (t : Finset β) (x : β → k) (e : β → ℕ) (hx : ∀ b ∈ t, x b ∈ J ^ e b) :
    ∏ b ∈ t, x b ∈ J ^ (∑ b ∈ t, e b) := by
  first | exact UpperTheory.Reformulated.B.Qk22.prod_mem_pow .. | (apply UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk22.prod_mem_pow <;> first | assumption | infer_instance)

theorem scCols_of (hSC : SCSt) : SCColsSt := by
  classical
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 n P hPint e he f hf
  refine Submodule.sum_mem _ fun mo hmo => ?_
  obtain ⟨r, hr⟩ := hPint mo
  rw [← hr, ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (pow_le_pow_right' (Submodule.one_le.mpr hJ1) (he mo hmo)
    (prod_mem_pow J _ _ _ fun b _ => ?_))
  refine hSC R d O k hRQ J hJ1 B h hcg w0 hw0 m ι π c s ξh ψ hH hψ h11 h21 h12 _ ?_ _ ?_ (f b) (hf b)
  · intro n'
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  · intro n' hn'
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn')]

theorem scaled_connection_columns (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCColsSt :=
  scCols_of (sc_of hN1 hN2 hN3)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

section
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed

theorem lemma_H_columns : ReciprocityTheory.ChartRestriction.G.TB.LemmaHColsSt :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.lemmaHCols_of Val.harmonic_value_integral ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

theorem symmetric_canonical_gauge : ReciprocityTheory.ChartRestriction.G.TB.SCSt :=
  ReciprocityTheory.ChartRestriction.G.TB.SCPf.sc_of ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_first_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

private theorem prod_mem_pow_of_mem_pow_of_sum_le {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (J : Submodule R A) (hJ : (1 : A) ∈ J) {n : ℕ} (x : Fin n → A) (a : Fin n → ℕ) (e : ℕ)
    (hx : ∀ b, x b ∈ J ^ a b) (ha : ∑ b, a b ≤ e) : ∏ b, x b ∈ J ^ e := by
  have hprod : ∀ s : Finset (Fin n), ∏ b ∈ s, x b ∈ J ^ (∑ b ∈ s, a b) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.one_le.mp le_rfl
    · intro i t hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
      exact Submodule.mul_mem_mul (hx i) ih
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le ha
  have h1 : (1 : A) ∈ J ^ c := by
    first
      | simpa using Submodule.pow_mem_pow J hJ c
      | simpa using Submodule.pow_mem_pow hJ c
  have hm := Submodule.mul_mem_mul (hprod Finset.univ) h1
  rwa [mul_one, ← pow_add, ← hc] at hm

theorem scaled_connection_columns : ReciprocityTheory.ChartRestriction.G.TB.SCColsSt :=
  by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hB w0 hw0 m ι π _ _ _ c s ξh ψ hξ hψ hp1 hp2 hp3 n P hPc e he f hf
  refine Submodule.sum_mem _ (fun mo _ => ?_)
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp (hPc mo)
  rw [← hr, ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (prod_mem_pow_of_mem_pow_of_sum_le J hJ1 _ _ e (fun b => ?_) (he mo ‹_›))
  refine symmetric_canonical_gauge R d O k hRQ J hJ1 B h hB w0 hw0 m ι π c s ξh ψ hξ hψ hp1 hp2 hp3 _ ?_ _ ?_ (f b) (hf b)
  · intro x
    classical
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro x hx
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hx)]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed
end
