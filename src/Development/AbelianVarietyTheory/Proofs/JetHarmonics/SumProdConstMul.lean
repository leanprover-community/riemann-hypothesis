import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DofIterSmulDir
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartEigenMemRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdLeadingMinors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfCongrJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstantCoeffDmonOfCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftUnpacking
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem sum_coeff_mul_weight {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]

theorem colValue_mul_of_disjoint_columns :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring

end GlobalTheory
end
end

section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CrudeValue

variable {k : Type} [CommRing k] {d : ℕ}

theorem constantCoeff_expS [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) :
    constantCoeff (FB.expS k g) = 1 := by
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [map_pow, hg, zero_pow hj, smul_zero]

theorem constantCoeff_ev_eq_zero {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have ha' : ∀ q : Fin m × Fin d, constantCoeff ((fun q : Fin m × Fin d => a q.1 q.2) q) = 0 :=
    fun q => ha q.1 q.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
    (hasSubst_of_constantCoeff_zero ha') ha' hf

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]

omit [Algebra ℚ k] in

theorem constantCoeff_hL (B : FB R d O) (h : PS k 2 d) (hh : constantCoeff h = 0) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have hp : ∀ i, constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => constantCoeff_X _
  refine constantCoeff_ev_eq_zero _ (fun j i => ?_) h hh
  fin_cases j
  · exact hp i
  · refine constantCoeff_ev_eq_zero ![pt k d 0] (fun j i' => ?_) (B.actK k w0 i) ?_
    · fin_cases j
      exact hp i'
    · unfold FB.actK
      rw [constantCoeff_map, B.A.const, map_zero]

theorem nabVal_monomial (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  · simp only [FB.nabVal, FB.FK, DpolyOf, MvPolynomial.support_monomial,
      if_neg (one_ne_zero : (1 : k) ≠ 0), Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_true, map_one, one_mul]

end GlobalTheory.CrudeValue

namespace GlobalTheory

open CrudeValue SymbolCols in

theorem sum_prod_nabVal_leading_minors : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  set g : Fin n → PS k 1 d := fun b =>
    ∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b) with hg
  have key := sum_prod_constantCoeff_dmonOf_cols R k (algebraMap R k) d B.G _ n u lam (fun _ => 1)
    al P g (fun b => C (c b) * E) hhom
    (fun b l l' hl ⟨mo, hmo, hl'⟩ => hpair b l l' (hsupp al halP l b hl) (hsupp mo hmo l' b hl'))
    (fun b mo _ => rfl)
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  refine Eq.trans (Finset.sum_congr rfl fun mo hmo => ?_) (key.trans ?_)
  · congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    have hle : (colM mo b).degree ≤ al.degree := by
      rw [← hdeg mo hmo, ← sum_degree_colM]
      exact Finset.single_le_sum (f := fun b => (colM mo b).degree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    rw [nabVal_monomial, ← hE, ← mul_assoc, mul_comm (g b)]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr al.degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hle)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  · simp only [h1, one_mul, one_pow, mul_one, map_mul, constantCoeff_C, hE1]
    rw [Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]

end GlobalTheory
end

section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

open CrudeValue SymbolCols in

theorem sum_prod_nabVal_leading_minors_of_column_jets : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ (colM al b).degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        if colM mo b = colM al b then (∏ l, ((al (l, b)).factorial : k)) * c b else 0 := by
    intro mo hmo b hb
    have hsym := constantCoeff_dmonOf_prod_linear R k (algebraMap R k) d B.G _ u (lam b)
      (fun _ => 1) (colM al b) (colM mo b) (C (c b) * E)
      (fun l l' hl hl' => hpair b l l' (hsupp al halP l b (by rwa [colM_apply] at hl))
        (hsupp mo hmo l' b (by rwa [colM_apply] at hl'))) hb
    simp only [colM_apply, one_pow, mul_one, map_mul, constantCoeff_C, hE1] at hsym
    rw [nabVal_monomial, ← hE, ← hsym, ← mul_assoc, mul_comm _ (C (c b))]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr (colM al b).degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hb)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  rw [Finset.sum_eq_single al]
  · rw [h1, one_mul, Finset.prod_congr rfl fun b _ => (hval al halP b le_rfl).trans (if_pos rfl),
      Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal'
    exact absurd halP hal'

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamGerm

namespace GlobalTheory.DepthBound

theorem minorMonomial_support {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ}
    (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (Z : T → Prop) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    {mo : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ} (hmo : mo ∈ (minorsP k col m).support) (l : Σ τ : T, Fin (r τ))
    (b : Fin n) (h : mo (l, b) ≠ 0) : Z l.1 ∧ ∃ i, col l.1 i = b := by
  have hS : minorsP k col m ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | Z x.1.1 ∧ ∃ i, col x.1.1 i = x.2} := by
    refine Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ => ?_
    by_cases hz : Z τ
    · exact Subalgebra.pow_mem _ (LeadingMinors.det_X_mem_supported _ _ fun a i => by exact ⟨hz, _, rfl⟩) _
    · rw [hm τ hz, pow_zero]; exact Subalgebra.one_mem _
  rw [MvPolynomial.mem_supported] at hS
  exact hS (Finset.mem_coe.2 ((MvPolynomial.mem_vars_iff_mem_support (l, b)).2
    ⟨mo, hmo, Finsupp.mem_support_iff.2 h⟩))

theorem map_minorsP {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) :
    MvPolynomial.map φ (minorsP k col m) = minorsP k' col m := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem eval_minorsP {k : Type} [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ)
    (y : (Σ τ : T, Fin (r τ)) × Fin n → k) :
    MvPolynomial.eval y (minorsP k col m) = ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) =>
      y (⟨τ, Fin.castLE s.isLt a⟩, col τ (Fin.castLE s.isLt i))).det ^ m τ s := by
  simp only [minorsP, map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 a i
  simp

theorem minorMonomial_add (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T]
    {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n) (m m' : ∀ τ, Fin (r τ) → ℕ) :
    minorsP k col (fun t s => m t s + m' t s) = minorsP k col m * minorsP k col m' := by
  simp only [minorsP, pow_add, Finset.prod_mul_distrib]

theorem sum_prod_restrict {k ι : Type} [CommRing k] [Fintype ι] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (ι × Fin n) k) (hP : ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S)
    (mu mu' : Fin n → (ι →₀ ℕ) → k) (h1 : ∀ mo ∈ P.support, ∀ b ∈ S, mu b (colM mo b) = mu' b (colM mo b))
    (h0 : ∀ b, b ∉ S → mu' b 0 = 1) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu' b (colM mo b) := by
  refine Finset.sum_congr rfl fun mo hmo => ?_
  rw [Finset.prod_congr rfl (h1 mo hmo), Finset.prod_subset (Finset.subset_univ S)]
  intro b _ hb
  have : colM mo b = 0 := Finsupp.ext fun l => by
    by_contra h
    exact hb (hP mo hmo l b h)
  rw [this, h0 b hb]

section Nab

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k] [Algebra ℚ k]
  [Algebra R k] (B : FB R d O) (h : PS k 2 d)

theorem nabVal_smul_dir (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (c : ι → k) (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) : B.nabVal k h w0 q f (fun l => c l • u l) (MvPolynomial.monomial mo 1) =
      (∏ l, c l ^ mo l) * B.nabVal k h w0 q f u (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one, DirScale.dmonOf_smul_dir, map_mul,
    constantCoeff_C]

theorem nabVal_C_mul (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : B.nabVal k h w0 q (C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold FB.nabVal
  rw [mul_assoc, GE.dpolyOf_Cmul_f, map_mul, constantCoeff_C]

theorem const_of_canon (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [WickVanishing.gt_const_ev_eq _ (WickVanishing.pair_points_zero_constant WickVanishing.gp_zero₂ (WickVanishing.gp_pt 0)), map_zero] at this

theorem nabVal_zero (hh : B.IsCanonGauge k h) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) : B.nabVal k h w0 q f u (MvPolynomial.monomial 0 1) = constantCoeff f := by
  have hA : ∀ b : O, WickVanishing.GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    WickVanishing.gt_const_ev _ (WickVanishing.pair_points_zero_constant (WickVanishing.gp_pt 0) (WickVanishing.gp_comp1 _ _ (hA w0) (WickVanishing.gp_pt 0))) h
      (const_of_canon B h hh)
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, ColumnValue.dmonOf_zero_index, map_mul,
    CrudeValue.constantCoeff_expS _ (by rw [WickVanishing.nt_const_smul, cL, mul_zero]), mul_one]

variable {R' : Type} [CommRing R'] [Algebra R' k] (φ : R →+* R') (hφ : (algebraMap R' k).comp φ = algebraMap R k)
include hφ

omit [Algebra ℚ k] in
theorem toK_map {n : ℕ} (f : PS R n d) : FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
  ext mo
  simp only [coeff_map, ← hφ, RingHom.comp_apply]

omit [Algebra ℚ k] in
theorem FK_map : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => toK_map φ hφ _

omit [Algebra ℚ k] in
theorem actK_map : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => toK_map φ hφ _

theorem isCanonGauge_map (hh : B.IsCanonGauge k h) : (FBMap.mapFB φ B).IsCanonGauge k h := by
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph1
  · rw [FK_map B φ hφ]; exact (toK_map φ hφ _).trans hh.ph2
  · exact (toK_map φ hφ _).trans hh.sy
  · rw [actK_map B φ hφ]; exact (toK_map φ hφ _).trans (hh.ad a)

omit [Algebra ℚ k] in
theorem hL_map : (FBMap.mapFB φ B).hL k h = B.hL k h := by
  funext w0; unfold FB.hL; rw [actK_map B φ hφ]

omit [Algebra ℚ k] in
theorem dAct_map : dAct k (FBMap.mapFB φ B) = dAct k B := by
  funext a; unfold dAct; rw [actK_map B φ hφ]

theorem nabVal_map (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial ι k) : (FBMap.mapFB φ B).nabVal k h w0 q f u P = B.nabVal k h w0 q f u P := by
  unfold FB.nabVal; rw [FK_map B φ hφ, hL_map B h φ hφ]

end Nab

section Val

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem mem_span_of_val_le (x y : TWO.Ov v) (hx : (x : F) ≠ 0) (h : v (x : F) ≤ v (y : F)) : y ∈ Ideal.span {x} := by
  have h0 : 0 ≤ v ((y : F) / x) := by
    by_contra hlt
    have e : v (y : F) = v ((y : F) / x) + v (x : F) := by rw [← v.map_mul, div_mul_cancel₀ _ hx]
    have hne : v (x : F) ≠ ⊤ := fun e' => hx (v.top_iff.1 e')
    have := WithTop.add_lt_add_right hne (not_le.1 hlt)
    rw [← e, zero_add] at this
    exact absurd h (not_le.2 this)
  refine Ideal.mem_span_singleton'.2 ⟨⟨(y : F) / x, h0⟩, Subtype.ext ?_⟩
  exact div_mul_cancel₀ _ hx

theorem val_le_of_mem_span {x y : TWO.Ov v} (h : y ∈ Ideal.span {x}) : v (x : F) ≤ v (y : F) := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  rw [Subring.coe_mul, v.map_mul]
  exact le_add_of_nonneg_left (TWO.v_nonneg v c)

theorem val_prod_le {κ : Type} (S : Finset κ) (x : κ → F) (r : κ → ℚ) (h : ∀ k ∈ S, v (x k) ≤ (r k : ℚ)) :
    v (∏ k ∈ S, x k) ≤ ((∑ k ∈ S, r k : ℚ) : WithTop ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, v.map_mul, WithTop.coe_add]
    exact add_le_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Val

theorem val_eigen_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (φ : R →+* TWO.Ov v)
    (hφ : (algebraMap (TWO.Ov v) F).comp φ = algebraMap R F) (B : FB R d O) (h : PS F 2 d) (hh : B.IsCanonGauge F h)
    (w0 a : O) (p k : ℕ) (hp0 : p ≠ 0) (hp : ¬ IsUnit (p : TWO.Ov v)) (hcop : ∃ u u' : O, u * a + u' * star a = 1)
    (ω : PS R 1 d) (hω1 : constantCoeff ω = 1)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ (c : O) l, (dAct F B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → τ t a ∈ Ideal.span {(p : TWO.Ov v)})
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v) (f : Fin n → PS (TWO.Ov v) 1 d)
    (hf0 : ∀ b ∈ S, v (constantCoeff (FB.toK F (f b))) = 0)
    (hf : ∀ b ∈ S, ∀ l, Z l.1 → ∀ mo, v (p : F) ≤ v (coeff mo (Dof (B.FK F) (fun i => (e l i : F)) (FB.toK F (f b)) -
      C (yy (l, b) : F) * FB.toK F (f b))))
    (γ ep : ℚ) (hep : v (p : F) = (ep : ℚ))
    (hy : ∀ t, Z t → ∀ s : Fin (rk t), v (((Matrix.of fun a i : Fin (s.val + 1) =>
      yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov v) : F) ≤ ((s.val + 1) * γ : ℚ))
    (hD : (∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ < ep) :
    v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
      B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial (colM mo b) 1)) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
  classical
  have hpF : ((p : TWO.Ov v) : F) = p := map_natCast (TWO.Ov v).subtype p
  have hmax : ∀ x ∈ Ideal.span {(p : TWO.Ov v)}, x ∈ IsLocalRing.maximalIdeal (TWO.Ov v) :=
    fun x hx => (Ideal.span_singleton_le_iff_mem _).2 hp hx
  let e₁ : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l => if Z l.1 then e l else 0
  let α : (Σ t, Fin (rk t)) → TWO.Ov v := fun l => if Z l.1 then τ l.1 a else 0
  let y₁ : (Σ t, Fin (rk t)) × Fin n → TWO.Ov v := fun x => if Z x.1.1 ∧ x.2 ∈ S then yy x else 0
  let f₁ : Fin n → PS (TWO.Ov v) 1 d := fun b => if b ∈ S then f b else 1
  have hB' := isCanonGauge_map B h φ hφ hh
  obtain ⟨ρ, hρ, hval⟩ := nabVal_columns_congr (TWO.Ov v) d O F (FBMap.mapFB φ B) h hB' w0 a p k
    (MvPowerSeries.map φ ω) (by rw [toK_map φ hφ, actK_map B φ hφ, hL_map B h φ hφ, hω])
    (Ideal.span {(p : TWO.Ov v)}) _ e₁ α
    (fun l => by
      by_cases hl : Z l.1
      · simpa only [α, if_pos hl] using hZ _ hl
      · simp only [α, if_neg hl]; exact Ideal.zero_mem _)
    (fun l => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · simp only [e₁, α, if_pos hl]; exact he a l
      · simp only [e₁, α, if_neg hl, Pi.zero_apply, map_zero, zero_smul]
        exact Matrix.mulVec_zero _)
    (fun l l' => by
      rw [dAct_map B φ hφ]
      by_cases hl : Z l.1
      · by_cases hl' : Z l'.1
        · simp only [e₁, if_pos hl, if_pos hl']
          obtain ⟨u, u', huu⟩ := hcop
          have h1 : τ l'.1 (star a) ∉ IsLocalRing.maximalIdeal (TWO.Ov v) := fun hx => by
            have := congrArg (τ l'.1) huu
            rw [map_add, map_mul, map_mul, map_one] at this
            exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 (this ▸
              Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmax _ (hZ _ hl'))) (Ideal.mul_mem_left _ _ hx)))
          have h2 : IsUnit (τ l.1 a - τ l'.1 (star a)) := by
            by_contra hx
            have := Ideal.sub_mem _ (hmax _ (hZ _ hl)) ((IsLocalRing.mem_maximalIdeal _).2 hx)
            rw [sub_sub_cancel] at this
            exact h1 this
          have h3 := bilinPart_eigen_mem_range (TWO.Ov v) d O F _ h hB' a (e l) (e l') _ _
            (by rw [dAct_map B φ hφ]; exact he a l) (by rw [dAct_map B φ hφ]; exact he (star a) l') h2
          have h4 := he w0 l'
          change (dAct F B w0).mulVec (fun i => algebraMap (TWO.Ov v) F (e l' i)) =
            algebraMap (TWO.Ov v) F (τ l'.1 w0) • fun i => algebraMap (TWO.Ov v) F (e l' i) at h4
          rw [h4, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
          exact Subring.mul_mem _ ⟨_, rfl⟩ h3
        · simp only [e₁, if_neg hl', Pi.zero_apply, map_zero]
          rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]
          exact Subring.zero_mem _
      · simp only [e₁, if_neg hl, Pi.zero_apply, map_zero]
        rw [show (fun _ : Fin d => (0 : F)) = 0 from rfl, zero_dotProduct]
        exact Subring.zero_mem _)
    n f₁ y₁
    (fun l b mo => by
      by_cases hl : Z l.1
      · by_cases hb : b ∈ S
        · refine mem_span_of_val_le v _ _ (by rw [hpF]; exact_mod_cast hp0) ?_
          rw [hpF]
          refine (hf b hb l hl mo).trans_eq (congrArg v ?_)
          simp only [e₁, f₁, y₁, if_pos hl, if_pos hb, if_pos (And.intro hl hb)]
          change _ = algebraMap (TWO.Ov v) F (coeff mo (Dof (FBMap.mapFB φ B).G.F (e l) (f b) - C (yy (l, b)) * f b))
          rw [← coeff_map]
          refine congrArg (coeff mo) (Eq.symm ?_)
          rw [map_sub, map_mul, map_C, InvDerMap.map_Dof, ← FK_map B φ hφ]
          rfl
        · simp [f₁, y₁, hb, Dof]
      · simp [e₁, y₁, hl, Dof])
    (minorsP (TWO.Ov v) col m)
  have hinj : Function.Injective (algebraMap (TWO.Ov v) F) := Subtype.val_injective
  rw [sum_prod_restrict S (minorsP F col m) (fun mo hmo l b hb => by
      obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
      exact hS _ i hz)
    (fun b mo => B.nabVal F h w0 (k * p) (FB.toK F (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
        (MvPolynomial.monomial mo 1))
    (fun b mo => (FBMap.mapFB φ B).nabVal F h w0 (p * k) (FB.toK F (f₁ b * MvPowerSeries.map φ ω ^ k))
      (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      have e1 : (fun l i => algebraMap (TWO.Ov v) F (e₁ l i)) =
          fun l => (if Z l.1 then (1 : F) else 0) • fun i => (e l i : F) := by
        funext l i
        by_cases hl : Z l.1 <;> simp [e₁, hl]
      have e2 : ∏ l, (if Z l.1 then (1 : F) else 0) ^ colM mo b l = 1 := Finset.prod_eq_one fun l _ => by
        by_cases hl : Z l.1
        · rw [if_pos hl, one_pow]
        · have : colM mo b l = 0 := by
            by_contra hx
            exact hl (minorMonomial_support col m Z hm hmo l b hx).1
          rw [this, pow_zero]
      beta_reduce
      rw [nabVal_map B h φ hφ, e1, nabVal_smul_dir, e2, one_mul, mul_comm p k, FB.toK, FB.toK, FB.toK, map_mul, map_pow,
        ← FB.toK, ← FB.toK, ← FB.toK, ← FB.toK, toK_map φ hφ]
      simp only [f₁, if_pos hb])
    (fun b hb => by
      beta_reduce
      rw [nabVal_zero _ h hB']
      simp [f₁, hb, hω1])]
  rw [← map_minorsP (algebraMap (TWO.Ov v) F), MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hval, map_add]
  have hmain : v (algebraMap (TWO.Ov v) F (MvPolynomial.eval y₁ (minorsP (TWO.Ov v) col m) *
      ∏ b, constantCoeff (f₁ b))) ≤ ((∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) : ℕ) * γ : ℚ) := by
    rw [map_mul, v.map_mul, map_prod, eval_minorsP, map_prod]
    refine (add_le_add (val_prod_le v _ _ (fun t => ∑ s : Fin (rk t), (m t s * (s.val + 1) : ℕ) * γ) fun t _ => ?_)
      (val_prod_le v _ _ (fun _ => 0) fun b _ => ?_)).trans (le_of_eq ?_)
    · rw [map_prod]
      refine val_prod_le v _ _ _ fun s _ => ?_
      rw [map_pow, v.map_pow]
      by_cases ht : Z t
      · have e3 : (Matrix.of fun a i : Fin (s.val + 1) =>
            y₁ (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))) = Matrix.of fun a i : Fin (s.val + 1) =>
            yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i)) := by
          ext1 a i
          exact if_pos ⟨ht, hS _ _ ht⟩
        rw [e3]
        refine (nsmul_le_nsmul_right (hy t ht s) _).trans (le_of_eq ?_)
        rw [← WithTop.coe_nsmul]
        congr 1
        push_cast
        ring
      · simp [hm t ht]
    · by_cases hb : b ∈ S
      · have := hf0 b hb
        rw [constantCoeff_map] at this
        simp only [f₁, if_pos hb, this]
        rfl
      · simp [f₁, hb]
    · rw [← WithTop.coe_add]
      congr 1
      simp [Finset.sum_mul]
  have hρ' : ((ep : ℚ) : WithTop ℚ) ≤ v (algebraMap (TWO.Ov v) F ρ) := by
    rw [← hep, ← hpF]; exact val_le_of_mem_span v hρ
  rw [v.map_add_eq_of_lt_left (lt_of_le_of_lt hmain (lt_of_lt_of_le (by exact_mod_cast hD) hρ'))]
  exact hmain

theorem val_factorial {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {p n : ℕ} (hp : p.Prime)
    (hpu : ¬ IsUnit (p : TWO.Ov v)) (hn : n < p) : v (n.factorial : F) = 0 := by
  have h1 : IsCoprime ((n.factorial : ℤ) : TWO.Ov v) ((p : ℤ) : TWO.Ov v) :=
    (Nat.isCoprime_iff_coprime.2 (hp.coprime_factorial_of_lt hn).symm).intCast
  obtain ⟨a, b, hab⟩ := h1
  have h2 : IsUnit ((n.factorial : ℕ) : TWO.Ov v) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact_mod_cast isUnit_of_mul_isUnit_right h
    · exact absurd (by exact_mod_cast isUnit_of_mul_isUnit_right h) hpu
  have h3 := TWO.v_unit v h2.unit
  rwa [IsUnit.unit_spec, show (((n.factorial : ℕ) : TWO.Ov v) : F) = n.factorial from
    map_natCast (TWO.Ov v).subtype _] at h3

theorem val_unit_columns {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {F : Type} [Field F]
    [CharZero F] [Algebra R F] (v : AddValuation F (WithTop ℚ)) (B : FB R d O) (h : PS F 2 d)
    (hh : B.IsCanonGauge F h) (w0 a : O) (p k : ℕ) (hp' : p.Prime) (hp : ¬ IsUnit (p : TWO.Ov v)) (ω : PS R 1 d)
    (hω : FB.toK F ω = FB.expS F (ev (n := 1) ![B.actK F a] (B.hL F h w0) - (p : F) • B.hL F h w0))
    {T : Type} [Fintype T] [DecidableEq T] {rk : T → ℕ} (τ : T → O →+* TWO.Ov v)
    (e : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (he : ∀ l, (dAct F B a).mulVec (fun i => (e l i : F)) = (τ l.1 a : F) • fun i => (e l i : F))
    (Z : T → Prop) (hZ : ∀ t, Z t → IsUnit (τ t a)) (lam : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v)
    (hlam : ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0)
    {n : ℕ} (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ)
    (hcol : ∀ t, Function.Injective (col t))
    (hS : ∀ t i, Z t → col t i ∈ S) (hm : ∀ t, ¬ Z t → ∀ s, m t s = 0)
    (hD : ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) < p) :
    ∃ (g : Fin n → PS F 1 d) (nb : Fin n → ℕ), (∀ b mo, 0 ≤ v (coeff mo (g b))) ∧
      ∑ b, nb b = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) ∧ ∀ f : Fin n → PS F 1 d,
      (∀ b ∈ S, ∀ mo : Fin 1 × Fin d →₀ ℕ, mo.degree ≤ nb b → coeff mo (f b) = coeff mo (g b)) →
      v (∑ mo ∈ (minorsP F col m).support, (minorsP F col m).coeff mo * ∏ b ∈ S,
        B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
          (MvPolynomial.monomial (colM mo b) 1)) = 0 := by
  classical
  let sc : (Σ t, Fin (rk t)) → (TWO.Ov v)ˣ := fun l => if hl : Z l.1 then (hZ _ hl).unit else 1
  let lam' : (Σ t, Fin (rk t)) → Fin d → TWO.Ov v := fun l i => ((sc l)⁻¹ : (TWO.Ov v)ˣ) * lam l i
  let u' : (Σ t, Fin (rk t)) → Fin d → F := fun l => ((sc l : TWO.Ov v) : F) • fun i => (e l i : F)
  obtain ⟨al, hal⟩ : ∃ al : (Σ t, Fin (rk t)) × Fin n →₀ ℕ, al = ∑ τ, ∑ s : Fin (rk τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (rk τ)),
      col τ (Fin.castLE s.isLt a)) 1 := ⟨_, rfl⟩
  obtain ⟨hc1, -, hdeg, -⟩ := LeadingMinors.coeff_prod_leading_minors F T rk n col m hcol (minorsP F col m) al rfl hal
  have hsup : al ∈ (minorsP F col m).support := MvPolynomial.mem_support_iff.2 (by rw [hc1]; exact one_ne_zero)
  have hcols : ∀ mo ∈ (minorsP F col m).support, ∀ l b, mo (l, b) ≠ 0 → b ∈ S := fun mo hmo l b hb => by
    obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m Z hm hmo l b hb
    exact hS _ i hz
  let g : Fin n → PS F 1 d := fun b =>
    ∏ l, (∑ i, C (lam' l i : F) * (X ((0 : Fin 1), i) : PS F 1 d)) ^ al (l, b)
  refine ⟨g, fun b => (colM al b).degree, fun b mo => ?_, (SymbolCols.sum_degree_colM al).trans hdeg, fun f hf => ?_⟩
  · have : g b = MvPowerSeries.map (algebraMap (TWO.Ov v) F)
        (∏ l, (∑ i, C (lam' l i) * (X ((0 : Fin 1), i) : PS (TWO.Ov v) 1 d)) ^ al (l, b)) := by
      simp only [map_prod, map_pow, map_sum, map_mul, map_C, map_X]
      rfl
    rw [this, coeff_map]
    exact TWO.v_nonneg v _
  let f₂ : Fin n → PS F 1 d := fun b => if b ∈ S then f b else g b
  have key := sum_prod_nabVal_leading_minors_of_column_jets R d O F B h (const_of_canon B h hh) w0 k T rk n col m hcol
    (minorsP F col m) al rfl hal u' (fun _ l i => (lam' l i : F)) (fun b l l' _ _ => by
      have h1 : ∑ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) = if l = l' then 1 else 0 := by
        have : ∀ i, lam' l i * ((sc l' : TWO.Ov v) * e l' i) =
            (((sc l)⁻¹ : (TWO.Ov v)ˣ) * (sc l' : TWO.Ov v)) * (lam l i * e l' i) := fun i => by
          simp only [lam']; ring
        simp only [this]
        rw [← Finset.mul_sum, hlam]
        split_ifs with hl
        · rw [hl, Units.inv_mul, mul_one]
        · rw [mul_zero]
      have h2 := congrArg (algebraMap (TWO.Ov v) F) h1
      rw [map_sum, apply_ite (algebraMap (TWO.Ov v) F), map_one, map_zero] at h2
      exact h2)
    (fun _ => 1) f₂ (fun b mo hmo => by
      rw [one_mul]
      by_cases hb : b ∈ S
      · simp only [f₂, if_pos hb]; exact hf b hb mo hmo
      · simp only [f₂, if_neg hb]; rfl)
  rw [sum_prod_restrict S (minorsP F col m) hcols
    (fun b mo => B.nabVal F h w0 (k * p) (ev (n := 1) ![B.actK F a] (f b) * FB.toK F ω ^ k) (fun l i => (e l i : F))
      (MvPolynomial.monomial mo 1))
    (fun b mo => B.nabVal F h w0 k (f₂ b) u' (MvPolynomial.monomial mo 1))
    (fun mo hmo b hb => by
      beta_reduce
      rw [mul_comm k p, nabVal_pullback_monomial R d O F B h hh w0 a p k ω hω _ _ (fun l => (τ l.1 a : F)) he,
        nabVal_smul_dir]
      simp only [f₂, if_pos hb]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : Z l.1
      · simp only [sc, dif_pos hl, IsUnit.unit_spec]
      · have : colM mo b l = 0 := by
          by_contra hx
          exact hl (minorMonomial_support col m Z hm hmo l b hx).1
        rw [this, pow_zero, pow_zero])
    (fun b hb => by
      beta_reduce
      have h0 : ∀ l, al (l, b) = 0 := fun l => by
        by_contra hx
        exact hb (hcols al hsup l b hx)
      rw [nabVal_zero _ h hh]
      simp only [f₂, if_neg hb, g, h0, pow_zero, Finset.prod_const_one, map_one]), key, Finset.prod_const_one, one_mul]
  refine Finset.prod_induction _ (fun x => v x = 0) (fun x x' hx hx' => by rw [v.map_mul, hx, hx', add_zero])
    v.map_one fun x _ => val_factorial v hp' hp (lt_of_le_of_lt (Finsupp.le_degree x al) (hdeg ▸ hD))

end GlobalTheory.DepthBound
end
end

section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem quad_add_zsmul (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (t : ℤ) : Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w := by
  have h1 := hQ (y + t • w)
  have h2 := hQ y
  have h3 := hQ w
  have h4 := hs w y
  simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul] at h1
  have h5 : 2 * Q (y + t • w) = 2 * (Q y + t * Bf y w + t ^ 2 * Q w) := by
    linear_combination h1 - h2 + t * h4 - t ^ 2 * h3
  exact mul_left_cancel₀ two_ne_zero h5

theorem quad_zero (hQ : ∀ x, 2 * Q x = Bf x x) : Q 0 = 0 := by
  have h := hQ 0
  simp only [map_zero] at h
  omega

theorem quad_nonneg (hQ : ∀ x, 2 * Q x = Bf x x) (hp : ∀ x, x ≠ 0 → 1 ≤ Q x) (x : X) :
    0 ≤ Q x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact (quad_zero hQ).ge
  · exact le_trans zero_le_one (hp x hx)

private lemma exists_int_shift_within_bounds (q B N a : ℤ) (hq : 0 < q) (hN : 0 < N) :
    ∃ m : ℤ, -(N * q) ≤ 2 * q * (a + N * m) + B ∧ 2 * q * (a + N * m) + B ≤ N * q := by
  have hD : 0 < 2 * q * N := by positivity
  have h1 := Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)
  have h2 := Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'
  have h3 := Int.emod_lt_of_pos (2 * q * a + B + N * q) hD
  refine ⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩
  · linarith
  · linarith

theorem quad_round_step (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (hw : 0 ≤ Q w) (N : ℤ) (hN : 0 < N) (a : ℤ) :
    ∃ m : ℤ, 4 * Q (y + (a + N * m) • w) ≤ 4 * Q y + N ^ 2 * Q w := by
  have key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w :=
    fun t => quad_add_zsmul hs hQ y w t
  rcases hw.lt_or_eq with hq | hq
  · obtain ⟨m, hm1, hm2⟩ := exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN
    refine ⟨m, ?_⟩
    rw [key]
    set t := a + N * m
    have hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2 := by
      nlinarith
    have hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w) := by
      nlinarith [sq_nonneg (Bf y w)]
    have := le_of_mul_le_mul_left hmul hq
    linarith
  · by_cases hB : 0 ≤ Bf y w
    · refine ⟨-|a|, ?_⟩
      rw [key, ← hq]
      have h1 : a + N * -|a| ≤ 0 := by
        nlinarith [le_abs_self a, abs_nonneg a]
      nlinarith
    · refine ⟨|a|, ?_⟩
      rw [key, ← hq]
      have h1 : 0 ≤ a + N * |a| := by
        nlinarith [neg_abs_le a, abs_nonneg a]
      nlinarith

theorem quad_round_sum (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    {ι : Type} [DecidableEq ι] (v : ι → X) (hv : ∀ j, 0 ≤ Q (v j)) (N : ℤ) (hN : 0 < N)
    (a : ι → ℤ) (s : Finset ι) :
    ∃ m : ι → ℤ, 4 * Q (∑ j ∈ s, (a j + N * m j) • v j) ≤ N ^ 2 * ∑ j ∈ s, Q (v j) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [quad_zero hQ]⟩
  | insert i s hi ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m0, h0⟩ :=
      quad_round_step hs hQ (∑ j ∈ s, (a j + N * m j) • v j) (v i) (hv i) N hN (a i)
    refine ⟨Function.update m i m0, ?_⟩
    have hs' : ∑ j ∈ s, (a j + N * Function.update m i m0 j) • v j
        = ∑ j ∈ s, (a j + N * m j) • v j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (fun h : j = i => hi (h ▸ hj))]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hs', Function.update_self, add_comm]
    nlinarith

theorem exists_pos_zsmul_mem_range {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (φ : X →+ X)
    (hφ : Function.Injective φ) (x : X) : ∃ N : ℤ, 0 < N ∧ ∃ y, φ y = N • x := by
  have : Module.Free ℤ X := Module.Free.of_basis b
  have : Module.Finite ℤ X := Module.Finite.of_basis b
  set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf
  set M := LinearMap.toMatrix b b f
  have hinj : Function.Injective f := by
    simpa [hf, AddMonoidHom.coe_toIntLinearMap] using hφ
  have hdet : M.det ≠ 0 := by
    intro h
    rw [LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (LinearMap.ker_eq_bot.mpr hinj)
  have e : Matrix.toLin b b M = f := Matrix.toLin_toMatrix b b f
  have key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id := by
    calc f.comp (Matrix.toLin b b M.adjugate)
        = (Matrix.toLin b b M).comp (Matrix.toLin b b M.adjugate) := by rw [e]
      _ = Matrix.toLin b b (M * M.adjugate) := (Matrix.toLin_mul b b b M M.adjugate).symm
      _ = M.det • LinearMap.id := by rw [Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
  refine ⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩
  have hx : f (Matrix.toLin b b M.adjugate x) = M.det • x := by
    have := congrArg (fun g => g x) key
    simpa using this
  have : φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x) := by
    rw [map_zsmul]; rfl
  rw [this, hx, smul_smul]

end CosetMin

theorem exists_coset_minimiser :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by
  classical
  intro X _ Bf Q hs hQ hp n b Cc hC φ g hg hφ x
  have hQφ : ∀ z, Q (φ z) = g * Q z := by
    intro z
    have h : 2 * Q (φ z) = 2 * (g * Q z) := by
      rw [hQ, hφ, ← hQ z]; ring
    exact mul_left_cancel₀ two_ne_zero h
  have hinj : Function.Injective φ := by
    intro u v huv
    by_contra hne
    have h0 : φ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have h1 := hp (u - v) (sub_ne_zero.mpr hne)
    have h2 := hQφ (u - v)
    rw [h0, quad_zero hQ] at h2
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg
    nlinarith
  obtain ⟨N, hN, y, hy⟩ := exists_pos_zsmul_mem_range b φ hinj x
  obtain ⟨m, hm⟩ := quad_round_sum hs hQ (fun j => φ (b j))
    (fun j => quad_nonneg hQ hp _) N hN (fun j => b.repr y j) Finset.univ
  set χ0 : X := ∑ j, m j • b j with hχ0
  have hNx : N • (x + φ χ0) = ∑ j, (b.repr y j + N * m j) • φ (b j) := by
    have hyφ : φ y = ∑ j, b.repr y j • φ (b j) := by
      calc φ y = φ (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
        _ = ∑ j, b.repr y j • φ (b j) := by rw [map_sum]; simp only [map_zsmul]
    rw [smul_add, ← hy, hyφ, hχ0, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, add_smul]
  have hsc : ∀ z : X, Q (N • z) = N ^ 2 * Q z := by
    intro z
    have := quad_add_zsmul hs hQ 0 z N
    simp only [zero_add, quad_zero hQ, map_zero, AddMonoidHom.zero_apply, mul_zero] at this
    linarith
  have hbound : 4 * Q (x + φ χ0) ≤ g * ∑ j, Q (b j) := by
    have h1 : 4 * Q (N • (x + φ χ0)) ≤ N ^ 2 * ∑ j, Q (φ (b j)) := by
      rw [hNx]; exact hm
    rw [hsc] at h1
    simp only [hQφ, ← Finset.mul_sum] at h1
    have hN2 : 0 < N ^ 2 := by positivity
    have h2 : N ^ 2 * (4 * Q (x + φ χ0)) ≤ N ^ 2 * (g * ∑ j, Q (b j)) := by linarith
    exact le_of_mul_le_mul_left h2 hN2
  have hex : ∃ k : ℕ, ∃ χ : X, Q (x + φ χ) = k :=
    ⟨(Q (x + φ χ0)).toNat, χ0, (Int.toNat_of_nonneg (quad_nonneg hQ hp _)).symm⟩
  obtain ⟨χ, hχ⟩ := Nat.find_spec hex
  have hmin : ∀ χ' : X, Q (x + φ χ) ≤ Q (x + φ χ') := by
    intro χ'
    rw [hχ]
    have := Nat.find_min' hex ⟨χ', (Int.toNat_of_nonneg (quad_nonneg hQ hp (x + φ χ'))).symm⟩
    calc (Nat.find hex : ℤ) ≤ ((Q (x + φ χ')).toNat : ℤ) := by exact_mod_cast this
      _ = Q (x + φ χ') := Int.toNat_of_nonneg (quad_nonneg hQ hp _)
  refine ⟨χ, ?_, ?_⟩
  · have h1 : 4 * Q (x + φ χ) ≤ g * ∑ j, Q (b j) := by linarith [hmin χ0]
    have h2 : (∑ j, (Q (b j) : ℝ)) ≤ n * Cc := by
      calc (∑ j, (Q (b j) : ℝ)) ≤ ∑ _j : Fin n, Cc := Finset.sum_le_sum fun j _ => hC j
        _ = n * Cc := by simp
    have h3 : 4 * (Q (x + φ χ) : ℝ) ≤ g * ∑ j, (Q (b j) : ℝ) := by exact_mod_cast h1
    have hg' : (0 : ℝ) ≤ g := by positivity
    nlinarith
  · intro q z
    have hz := hmin (χ + z)
    rw [map_add, ← add_assoc] at hz
    have e1 := quad_add_zsmul hs hQ (x + φ χ) (φ z) 1
    have e2 := quad_add_zsmul hs hQ (x + φ χ) (φ z) q
    rw [one_smul] at e1
    rw [natCast_zsmul] at e2
    rw [e2]
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem exists_transl_smul (hL : Laws) (q : ℕ) (hq : 1 ≤ q) (c : 𝓞 E) (s : Fam y.P.D.toPre F q) :
    ∃ u : F, y.v u = 0 ∧ y.Transl q c s (u • s) := by
  let _ := H.starRing
  have hG := hL.globalFns
  obtain ⟨f, hf1, -, -, hf4, -⟩ := y.tors F q hq
  obtain ⟨p0, hp0y, -, hp0a⟩ := CanonicalLiftUnpacking.exists_zero_qk (D := y.P.D.toPre) (F := F) y.P.D.tau_bimult q
  have hf0 : f p0 = 1 := by
    have := hf4 p0 p0 p0 ⟨p0, by rw [hp0y, add_zero], hp0a, qk_equiv_refl y.P.D.tau_bimult p0⟩
    exact mul_eq_left.1 this.symm
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p0.g.b)
      (DegPre.lineε q)), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F q hq p0 w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ y.P.D F q hq p0 w hw
  obtain ⟨w₂, hw₂, hc⟩ := ThetaMul.phi_mul_core hG p0 p0 p0 (by rw [hp0y, add_zero]) hp0a w w hw hw
  obtain ⟨e, he⟩ := ThetaFinOrd.exists_scalar hG p0 w₂ w hw₂ hw (Φ * Φ : Module.End F (Fam y.P.D.toPre F q)) Φ
    (fun s => hc s _ _ ((hΦ _ _).2 rfl) ((hΦ _ _).2 rfl)) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p0 w ζ Φ hΦ).1 hfin
  have hsc : ∀ t, Φ t = e • t := fun t => by
    obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have h1 := LinearMap.congr_fun hU t
    rw [pow_succ', Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    have h2 := LinearMap.congr_fun he (((ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) ^ M) t)
    rw [Module.End.mul_apply, LinearMap.smul_apply] at h2
    rw [← h1, map_smul, h2, smul_comm]
  have hT : y.Transl q c s ((ζ * e) • s) := by
    refine ⟨p0, 1, w, ζ, Φ s, (hf1 _ _).2 hf0.symm, ?_, hw, hζ, hfin, (hΦ _ _).2 rfl, ?_⟩
    · have := y.P.oA.hom c
      exact MonObj.one_comp _
    · rw [DVR.isSmul_iff, hsc, smul_smul]
  by_cases hs : s = 0
  · refine ⟨1, y.v.map_one, ?_⟩
    rw [hs, smul_zero] at hT ⊢
    exact hT
  · refine ⟨ζ * e, ?_, hT⟩
    have h1 : (ζ • Φ : Module.End F (Fam y.P.D.toPre F q)) = (ζ * e) • 1 := LinearMap.ext fun t => by
      rw [LinearMap.smul_apply, hsc, smul_smul]; rfl
    have h2 := LinearMap.congr_fun hU s
    rw [h1, smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at h2
    have h3 : (ζ * e) ^ M = 1 := by
      have : ((ζ * e) ^ M - 1) • s = 0 := by rw [sub_smul, h2, one_smul, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hs)
    have h4 := congrArg y.v h3
    rw [y.v.map_pow, y.v.map_one] at h4
    induction hx : y.v (ζ * e) using WithTop.recTopCoe with
    | top =>
      obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [hx, succ_nsmul, add_top] at h4
      exact h4
    | coe x =>
      rw [hx, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h4
      rw [h4.resolve_left (by omega)]; rfl

variable [CharZero F] [Algebra V F] [IsScalarTower V (FractionRing V) F]

omit [IsAlgClosed F] [CharZero F] in
theorem fO_comp_eq : (algebraMap (TWO.Ov y.v) F).comp (TWO.fO y.v y.hϖ y.hv) = algebraMap V F :=
  (IsScalarTower.algebraMap_eq V (FractionRing V) F).symm

theorem exists_jet_column (hL : Laws) (hG : FamGerm.GermExSt) (hJ : JetsSt) (hP : PullGermSt) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (N k n : ℕ)
    (hN : 1 ≤ N) (haa : letI := H.starRing; a * star a = (N : 𝓞 E)) (hn : 4 * n + 4 ≤ k) (hM : (n : ℝ) * M₀ < k)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0))
    (g : PS F 1 y.d) (hg : ∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * N)) (c : F) (f : PS F 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k N s s' ∧ y.Transl (k * N) (star a) s' t ∧
        y.Germ (k * N) t (MvPowerSeries.C c * (ev (n := 1) ![y.B.actK F a] f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ (n : ℝ) ^ 2 * Cc / k ∧
      ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  obtain ⟨G, hGm⟩ := hG E H V F y (k * N) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a N k hN hk1 haa
  obtain ⟨gm, h0, h1, h2⟩ := hJ E H V F y r bs Cc M₀ hred k n hn hM
  obtain ⟨s, f, h3, h4, -, h6⟩ := h2 g hg
  obtain ⟨w, κ, hw, hpull⟩ := hP E H V F y a N k hN (by omega) haa h hh
  obtain ⟨τ, hτ⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv h0
  obtain ⟨u, hu, hT⟩ := exists_transl_smul y hL (k * N) hkN (star a) (π (τ • s))
  have hnu : NuGe y.P.D y.Q F y.v k (τ • s) 0 := by
    have := NuGe.smul y.Q (s' := τ • s) hτ.ge (fun _ _ => rfl) h3
    rwa [neg_add_cancel] at this
  have hκ : y.v (algebraMap V F κ) = 0 := by
    rw [← fO_comp_eq y]
    exact TWO.v_unit y.v (Units.map (TWO.fO y.v y.hϖ y.hv : V →* TWO.Ov y.v) κ)
  refine ⟨τ • s, π (τ • s), _, u * τ * algebraMap V F κ, f, gm, ⟨hnu, (hπ _ _).2 rfl, hT, (hGm _ _).2 ?_⟩, ?_, h1, h6⟩
  · rw [map_smul, map_smul, map_smul, ← (hGm _ _).1 (hpull s _ f ((hπ _ _).2 rfl) h4), hw.trans hω.symm,
      MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul]
    simp only [map_mul, _root_.mul_assoc]
  · rw [y.v.map_mul, y.v.map_mul, hu, hτ, hκ, zero_add, add_zero]

theorem exists_eigen_column (hL : Laws) (hTW : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hUU : UUStatement)
    (hG : FamGerm.GermExSt) (hV : GermValSt) (hE : EigGermSt) (Dw : Datum H)
    (I : letI := H.starRing; TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a)
      (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))) (r : ℕ)
    (bs : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) (hred : y.Red r bs Cc M₀) (a : 𝓞 E) (p k : ℕ)
    (hp : p.Prime) (hk : 4 ≤ k) (haa : letI := H.starRing; a * star a = (p : 𝓞 E))
    (hcop : letI := H.starRing; ∃ u u' : 𝓞 E, u * a + u' * star a = 1) (hpk : Nat.Coprime p k)
    (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy α : Λ → TWO.Ov y.v)
    (hα : ∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)})
    (he : letI := H.starRing; ∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F))
    (hc : y.CharAt a p e yy)
    (h : PS F 2 y.d) (hh : letI := H.starRing; y.B.IsCanonGauge F h) (ω : PS V 1 y.d)
    (hω1 : MvPowerSeries.constantCoeff ω = 1)
    (hω : letI := H.starRing; FB.toK F ω =
      FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0)) :
    letI := H.starRing
    ∃ (s : Fam y.P.D.toPre F k) (s' t : Fam y.P.D.toPre F (k * p)) (c : F) (f : PS (TWO.Ov y.v) 1 y.d) (r₀ : ℚ),
      (NuGe y.P.D y.Q F y.v k s 0 ∧ PullAl y.P.D F y.P.oD a k p s s' ∧ y.Transl (k * p) (star a) s' t ∧
        y.Germ (k * p) t (MvPowerSeries.C c * (FB.toK F f * FB.toK F ω ^ k))) ∧
      y.v c = (r₀ : ℚ) ∧ (r₀ : ℝ) ≤ r * Cc / (4 * k) ∧ y.v (MvPowerSeries.constantCoeff (FB.toK F f)) = 0 ∧
      ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) (FB.toK F f) -
        MvPowerSeries.C (yy l : F) * FB.toK F f)) := by
  let _ := H.starRing
  have hk1 : 1 ≤ k := by omega
  have hN : 1 ≤ p := hp.pos
  have hkN : 1 ≤ k * p := Nat.mul_pos hk1 hN
  have haa' : star a * a = (p : 𝓞 E) := by rw [mul_comm, haa]
  have hQa := QuadraticAlgebraValuation.qAl_of hL V y.ϖ y.hϖ y.P.D y.Q y.hQ (𝓞 E) y.P.oD a p haa haa'
  obtain ⟨G, hGm⟩ := hG E H V F y (k * p) hkN
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V y.P.D F (𝓞 E) y.P.oD H.w0 y.P.w0 a p k hN hk1 haa
  obtain ⟨pt, x, hpt, hx, hE'⟩ := hE E H V F y a p k hp hk haa Λ e yy α hα he hc Dw I hpk hcop
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b)
      (DegPre.lineε (k * p))), w.IsGen := ClosedPointWeilPower.gen_local_linComb y.P.D.toPre.P.L y.P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := finOrdExists_of_laws hL V y.P.D F _ hkN pt w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V _ y.P.D F _ hkN pt w hw
  obtain ⟨χ₀, hχ1, hχ2⟩ := exists_coset_minimiser y.P.D.toPre.X (QForm.bHom y.hϖ y.P.D y.hQ) y.Q
    (fun _ _ => QForm.bOf_comm y.P.D _ _) (QForm.two_Q_eq y.hϖ y.P.D y.hQ)
    (fun _ hx => QForm.Q_pos y.hϖ y.P.D y.hQ hx) r bs Cc hred.2.2.1 (DistribSMul.toAddMonoidHom _ (star a)) p hN
    (fun x x' => by
      simp only [QForm.bHom_apply, QForm.bOf, DistribSMul.toAddMonoidHom_apply, ← smul_add, hQa]
      ring) pt.y
  simp only [DistribSMul.toAddMonoidHom_apply] at hχ1 hχ2
  obtain ⟨s, hs, hex⟩ := ExactTerm.main hL hTW hVR hUU V y.ϖ y.hϖ y.P.D y.Q y.hQ F y.v y.hv (𝓞 E) y.P.oD H.w0 y.P.w0
    a p k hN hk haa pt w hw ζ hζ hfin χ₀
  have hsm : Fam.IsSmul y.P.D.toPre F ζ (Φ (π s)) (ζ • Φ (π s)) := (DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨hnu, hsupp, c, hc0, hcv⟩ := hex (π s) (Φ (π s)) _ ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) hsm
  set t := ζ • Φ (π s) with ht
  set r₀ : ℚ := (y.Q (star a • χ₀ + pt.y) : ℚ) / (k * p) with hr₀
  have hkp : (0 : ℚ) < k * p := by exact_mod_cast hkN
  have hother : ∀ β, β ≠ star a • χ₀ + pt.y → VGe y.P.D F y.v (k * p) β (t.s β) (r₀ + 1 / (k * p)) := by
    intro β hβ
    by_cases hz : ∃ z, β = pt.y + star a • χ₀ + k • star a • z
    · obtain ⟨z, rfl⟩ := hz
      refine (hnu _).mono ?_
      have hz0 : star a • z ≠ 0 := fun h0 => hβ (by rw [h0, smul_zero, add_zero, add_comm])
      have h1 := QForm.Q_pos y.hϖ y.P.D y.hQ hz0
      have h2 := hχ2 k z
      have h3 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) * y.Q (star a • z) := by
        have : (4 : ℤ) ≤ k := by exact_mod_cast hk
        have h5 : (1 : ℤ) ≤ (k : ℤ) * (k - 1) := by nlinarith
        nlinarith
      have h4 : (y.Q (star a • χ₀ + pt.y) : ℚ) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z) := by
        rw [add_comm (star a • χ₀)]
        exact_mod_cast (by linarith : y.Q (pt.y + star a • χ₀) + 1 ≤ y.Q (pt.y + star a • χ₀ + k • star a • z))
      rw [hr₀, zero_add, ← add_div, Nat.cast_mul]
      exact div_le_div_of_nonneg_right h4 hkp.le
    · exact vge_of_zero (hsupp β fun z e => hz ⟨z, e⟩) _
  have hall : ∀ β, VGe y.P.D F y.v (k * p) β (t.s β) r₀ := fun β => by
    by_cases hβ : β = star a • χ₀ + pt.y
    · subst hβ
      refine (hnu _).mono (le_of_eq ?_)
      rw [hr₀, zero_add, Nat.cast_mul]
    · exact (hother β hβ).mono (le_add_of_nonneg_right (by positivity))
  obtain ⟨hV1, hV2⟩ := hV E H V F y (k * p) hkN t (G t) ((hGm _ _).2 rfl)
  have hV1' := hV1 r₀ hall
  have hV2' := hV2 _ c r₀ _ hc0 hcv (lt_add_of_pos_right _ (by positivity)) hother
  have hcne : c ≠ 0 := fun h0 => by
    rw [h0, y.v.map_zero] at hcv
    exact WithTop.top_ne_coe hcv
  have hci : y.v c⁻¹ = ((-r₀ : ℚ) : WithTop ℚ) := by
    rw [y.v.map_inv, hcv]; rfl
  let f₀ : PS (TWO.Ov y.v) 1 y.d := fun mo => ⟨c⁻¹ * MvPowerSeries.coeff mo (G t), by
    rw [TWO.mem_Ov, y.v.map_mul, hci]
    refine le_trans (le_of_eq ?_) (add_le_add le_rfl (hV1' mo))
    rw [← WithTop.coe_add, neg_add_cancel]; rfl⟩
  have hf₀ : FB.toK F f₀ = MvPowerSeries.C c⁻¹ * G t := by
    ext mo
    rw [MvPowerSeries.coeff_C_mul]; rfl
  obtain ⟨ω', hω'⟩ := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hω1 ▸ isUnit_one) : IsUnit ω).exists_left_inv
  have hω'1 : MvPowerSeries.constantCoeff ω' = 1 := by
    have := congrArg MvPowerSeries.constantCoeff hω'
    rwa [map_mul, hω1, _root_.mul_one, map_one] at this
  have hmap : FB.toK F (MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω') = FB.toK F ω' := by
    ext mo
    simp only [MvPowerSeries.coeff_map, ← fO_comp_eq y, RingHom.comp_apply]
  have hsp : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) =
      MvPowerSeries.C c⁻¹ * G t * FB.toK F ω' ^ k := by
    rw [← hf₀, ← hmap]
    exact (map_mul _ _ _).trans (congrArg _ (map_pow _ _ _))
  have hωω : FB.toK F ω' * FB.toK F ω = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, hω', map_one]
  have hf : FB.toK F (f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k) * FB.toK F ω ^ k =
      MvPowerSeries.C c⁻¹ * G t := by
    rw [hsp, _root_.mul_assoc, ← mul_pow, hωω, one_pow, _root_.mul_one]
  refine ⟨s, π s, t, c, f₀ * MvPowerSeries.map (TWO.fO y.v y.hϖ y.hv) ω' ^ k, r₀, ⟨hs, (hπ _ _).2 rfl,
    ⟨pt, x, w, ζ, _, hpt, hx, hw, hζ, hfin, (hΦ _ _).2 rfl, hsm⟩, (hGm _ _).2 ?_⟩, hcv, ?_, ?_, ?_⟩
  · rw [hf, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hcne, map_one, _root_.one_mul]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hN
    rw [hr₀, add_comm (star a • χ₀)]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    refine hχ1.trans (le_of_eq ?_)
    field_simp
  · rw [hsp]
    simp only [FB.toK, map_mul, map_pow, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_map, hω'1, map_one,
      one_pow, _root_.mul_one]
    rw [y.v.map_mul, hci, hV2', ← WithTop.coe_add, neg_add_cancel]; rfl
  · have hct : (c⁻¹ * ζ) • Φ (π s) = c⁻¹ • t := by rw [ht, smul_smul]
    refine hE' w hw s (π s) (Φ (π s)) (c⁻¹ * ζ) ((hπ _ _).2 rfl) ((hΦ _ _).2 rfl) (fun χ => ?_) h ω hh hω _ ?_
    · rw [hct]
      have := (hall χ).smul (s' := (c⁻¹ • t).s χ) hci.ge (fun _ => rfl)
      rwa [add_neg_cancel] at this
    · rw [hct, hf, hGm, G.map_smul c⁻¹ t, MvPowerSeries.smul_eq_C_mul]

end GlobalTheory.DepthBound
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

theorem sum_prod_const_mul {k Λ : Type} [CommRing k] [Fintype Λ] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (Λ × Fin n) k) (mu mu' : Fin n → (Λ →₀ ℕ) → k) (c : Fin n → k)
    (h : ∀ b ∈ S, ∀ mo, mu b mo = c b * mu' b mo) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      (∏ b ∈ S, c b) * ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu' b (colM mo b) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b hb => h b hb _, Finset.prod_mul_distrib]
  ring

end GlobalTheory.DepthBound
end
end
