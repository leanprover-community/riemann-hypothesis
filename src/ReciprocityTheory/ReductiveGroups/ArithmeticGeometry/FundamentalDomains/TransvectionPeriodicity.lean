import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs

section
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section gram

variable (X : Data E r)

def hv (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Fin r → ℂ :=
  fun a => hermC τ.1 X.Gm (col M a) (Data.emb τ.1 ξ)

def rk1 (ξ : Fin r → E) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  vecMulVec (hv X ξ τ M) (fun b => conj (hv X ξ τ M b))

lemma col_mul (A M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * M) a = A *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

private lemma hermC_add_smul_add_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u e v : Fin r → ℂ)
    (β γ : ℂ) :
    hermC τ G (u + β • e) (v + γ • e) = hermC τ G u v + conj γ * hermC τ G u e +
      β * hermC τ G e v + β * conj γ * hermC τ G e e := by
  simp only [hermC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma hermC_swap_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → ℂ) :
    hermC τ G v u = conj (hermC τ G u v) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← emb_cc', hG]
  ring

lemma hermC_pair (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (e u v : Fin r → ℂ) (he : hermC τ G e e = 0) (α : ℂ) :
    hermC τ G (u + (α * hermC τ G u e) • e) (v + (α * hermC τ G v e) • e) =
      hermC τ G u v + (α + conj α) * hermC τ G u e * conj (hermC τ G v e) := by
  rw [hermC_add_smul_add_smul, hermC_swap_of_conj_symm τ G hG v e, he]
  simp only [map_mul]
  ring

lemma alpha_conj (c : ℝ) (s : ℂ) :
    (-(I * (c : ℂ) * s)) + conj (-(I * (c : ℂ) * s)) = ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private lemma hermC_emb_emb_eq_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc']

lemma gram_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  have he : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_herm, hξ, map_zero]
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1, hv,
    vecMulVec_apply]
  rw [col_mul, col_mul, flowMat_mulVec (X := X), flowMat_mulVec (X := X),
    hermC_pair τ.1 X.Gm X.Gm_herm _ _ _ he, alpha_conj]
  ring

lemma mat_flow (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl

def admissibleImaginary (ξ : Fin r → E) (x : Frame X.Ψ r) : Set (X.Ψ → ℝ) :=
  {y | ∀ τ : X.Ψ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i *
    (lminor (gram τ.1 X.Gm (mat x τ) + ((2 * X.c τ * y τ : ℝ) : ℂ) • rk1 X ξ τ (mat x τ)) i).re}

lemma flow_mem_dom_iff {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) :
    X.flow ξ s x ∈ X.dom ↔ (fun τ => (s τ).im) ∈ admissibleImaginary X ξ x := by
  simp only [Data.dom, GG, Set.mem_setOf_eq, admissibleImaginary, dmin, mat_flow, gram_flowMat X hξ, det_mul,
    det_flowMat (X := X) hξ, one_mul]
  constructor
  · intro h τ i
    exact (h τ).2 i
  · intro h τ
    exact ⟨(hx τ).1, h τ⟩

end gram

section affine

lemma leadingMinor_add_rankOne (A : Matrix (Fin r) (Fin r) ℂ) (u v : Fin r → ℂ) (i : Fin (r + 1))
    (hA : lminor A i ≠ 0) : ∃ κ : ℂ, ∀ t : ℂ, lminor (A + t • vecMulVec u v) i = lminor A i * (1 + t * κ) := by
  unfold lminor at hA ⊢
  set e := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  set B := A.submatrix e e with hB
  have hB' : IsUnit B.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨(v ∘ e) ⬝ᵥ (B⁻¹ *ᵥ (u ∘ e)), fun t => ?_⟩
  have hz : B *ᵥ (B⁻¹ *ᵥ (u ∘ e)) = u ∘ e := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hB', one_mulVec]
  have key : B * (1 + vecMulVec (B⁻¹ *ᵥ (u ∘ e)) (t • (v ∘ e))) =
      (A + t • vecMulVec u v).submatrix e e := by
    rw [mul_add, mul_one]
    ext a b
    have hza : ∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k = u (e a) := congrFun hz a
    simp only [Matrix.add_apply, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Function.comp_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rw [show ∑ k, B a k * ((B⁻¹ *ᵥ (u ∘ e)) k * (t * v (e b))) =
        (∑ k, B a k * (B⁻¹ *ᵥ (u ∘ e)) k) * (t * v (e b)) by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring, hza]
    simp only [hB, Matrix.submatrix_apply]
    ring
  rw [← key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul]

lemma open_convex_aff {ι κ : Type*} [Fintype ι] [Finite κ] (a b : ι → κ → ℝ) :
    IsOpen {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} ∧
      Convex ℝ {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  constructor
  · have hs : {y : ι → ℝ | ∀ τ i, 0 < a τ i + y τ * b τ i} =
        ⋂ τ, ⋂ i, {y : ι → ℝ | 0 < a τ i + y τ * b τ i} := by
      ext y
      simp
    rw [hs]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_const.add ((continuous_apply τ).mul continuous_const))
  · intro y hy z hz s t hs ht hst
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hy hz ⊢
    intro τ i
    have h1 := hy τ i
    have h2 := hz τ i
    have key : a τ i + (s * y τ + t * z τ) * b τ i =
        s * (a τ i + y τ * b τ i) + t * (a τ i + z τ * b τ i) := by
      linear_combination (-(a τ i)) * hst
    rw [key]
    rcases hs.lt_or_eq with hs' | hs'
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h1) (mul_nonneg ht h2.le)
    · subst hs'
      have ht1 : t = 1 := by linarith
      subst ht1
      simpa using h2

end affine

section adm

variable (X : Data E r)

lemma admissibleImaginary_eq_halfspaces {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by
  have hL : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), lminor (gram τ.1 X.Gm (mat x τ)) i ≠ 0 := by
    intro τ i h
    have h1 := (hx τ).2 i
    simp only [dmin, h, Complex.zero_re, mul_zero, lt_irrefl] at h1
  have hk : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), ∃ κ : ℂ, ∀ t : ℂ,
      lminor (gram τ.1 X.Gm (mat x τ) + t • rk1 X ξ τ (mat x τ)) i =
        lminor (gram τ.1 X.Gm (mat x τ)) i * (1 + t * κ) :=
    fun τ i => leadingMinor_add_rankOne _ _ _ i (hL τ i)
  choose κ hκ using hk
  have hre : ∀ (L k : ℂ) (t : ℝ), (L * (1 + (t : ℂ) * k)).re = L.re + t * (L * k).re := by
    intro L k t
    rw [show L * (1 + (t : ℂ) * k) = L + (t : ℂ) * (L * k) by ring, Complex.add_re,
      Complex.re_ofReal_mul]
  refine ⟨fun τ i => psgn X.p0 i * (lminor (gram τ.1 X.Gm (mat x τ)) i).re,
    fun τ i => psgn X.p0 i * (2 * X.c τ) * (lminor (gram τ.1 X.Gm (mat x τ)) i * κ τ i).re, ?_⟩
  ext y
  simp only [admissibleImaginary, Set.mem_setOf_eq, hκ, hre]
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  apply iff_of_eq
  congr 1
  ring

lemma admissibleImaginary_open_convex {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    IsOpen (admissibleImaginary X ξ x) ∧ Convex ℝ (admissibleImaginary X ξ x) := by
  obtain ⟨a, b, h⟩ := admissibleImaginary_eq_halfspaces X (ξ := ξ) x hx
  rw [h]
  exact open_convex_aff a b

end adm

end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]


lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
end
