import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaEisensteinConvergeBounded
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCusps
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilAction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperator
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHigh
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
import BuildAid.ForwardExisting

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Emb

noncomputable section

section Corner

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

def cor (c : R) (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (A i') j) i

@[simp] theorem corner_embedding_succ_succ (c : R) (A : Matrix (Fin N) (Fin N) R) : cor c A 0 0 = c := rfl
@[simp] theorem cor_zs (c : R) (A : Matrix (Fin N) (Fin N) R) (j : Fin N) :
    cor c A 0 j.succ = 0 := rfl
@[simp] theorem cor_sz (c : R) (A : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    cor c A i.succ 0 = 0 := rfl
@[simp] theorem cor_ss (c : R) (A : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    cor c A i.succ j.succ = A i j := rfl

theorem cor_mul (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A * cor b B = cor (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem cor_add (a b : R) (A B : Matrix (Fin N) (Fin N) R) :
    cor a A + cor b B = cor (a + b) (A + B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_neg (a : R) (A : Matrix (Fin N) (Fin N) R) : -cor a A = cor (-a) (-A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_one : cor (1 : R) (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]

theorem cor_zero : cor (0 : R) (0 : Matrix (Fin N) (Fin N) R) = 0 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_map (f : R →+* S) (a : R) (A : Matrix (Fin N) (Fin N) R) :
    (cor a A).map f = cor (f a) (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp

theorem cor_conjTranspose (a : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (cor a A)ᴴ = cor (conj a) Aᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

theorem cor_mulVec (a : R) (A : Matrix (Fin N) (Fin N) R) (x : R) (v : Fin N → R) :
    cor a A *ᵥ (Fin.cons x v : Fin (N + 1) → R) = (Fin.cons (a * x) (A *ᵥ v) : Fin (N + 1) → R) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem cons_dot (x y : R) (v w : Fin N → R) :
    (Fin.cons x v : Fin (N + 1) → R) ⬝ᵥ (Fin.cons y w : Fin (N + 1) → R) = x * y + v ⬝ᵥ w := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem cor_inv (A : Matrix (Fin N) (Fin N) ℂ) (h : A.det ≠ 0) : (cor 1 A)⁻¹ = cor 1 A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [cor_mul, one_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h), cor_one]

theorem det_cor_den (C D : Matrix (Fin N) (Fin N) R) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (cor 0 C * Z + cor 1 D).det = (C * Z.submatrix Fin.succ Fin.succ + D).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have e : (cor 0 C * Z + cor 1 D).submatrix Fin.succ (Fin.succAbove 0) = C * Z.submatrix Fin.succ Fin.succ + D := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  rw [e]
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_cor_one (D : Matrix (Fin N) (Fin N) R) : (cor 1 D).det = D.det := by
  simpa using det_cor_den (0 : Matrix (Fin N) (Fin N) R) D 0

theorem posDef_cor_one (A : Matrix (Fin N) (Fin N) ℂ) (h : A.PosDef) : (cor 1 A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.IsHermitian, cor_conjTranspose, h.1.eq]
    simp
  · obtain ⟨a, v, rfl⟩ : ∃ (a : ℂ) (v : Fin N → ℂ), x = Fin.cons a v :=
      ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have hs : star (Fin.cons a v : Fin (N + 1) → ℂ) = Fin.cons (star a) (star v) := by
      ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [cor_mulVec, hs, cons_dot, one_mul]
    by_cases hv : v = 0
    · subst hv
      have ha : a ≠ 0 := by
        rintro rfl; exact hx (by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp)
      simp only [Matrix.mulVec_zero, dotProduct_zero, add_zero]
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast Complex.normSq_pos.mpr ha
    · have h1 : 0 ≤ star a * a := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact_mod_cast Complex.normSq_nonneg a
      exact add_pos_of_nonneg_of_pos h1 (h.dotProduct_mulVec_pos hv)

theorem imH_cor (A : Matrix (Fin N) (Fin N) ℂ) : imH (cor I A) = cor 1 (imH A) := by
  unfold imH
  rw [cor_conjTranspose]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp
  field_simp
  rw [Complex.I_sq]
  ring

end Corner

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

def emb (γ : M2 E N) : M2 E (N + 1) :=
  Matrix.fromBlocks (cor 1 γ.toBlocks₁₁) (cor 0 γ.toBlocks₁₂) (cor 0 γ.toBlocks₂₁)
    (cor 1 γ.toBlocks₂₂)

theorem ccT_cor (a : E) (A : Matrix (Fin N) (Fin N) E) : ccT (cor a A) = cor (cc a) (ccT A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [ccT, cc]

theorem ccT_fromBlocks {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) E) :
    ccT (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (ccT A) (ccT C) (ccT B) (ccT D) := by
  simp [ccT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

private theorem fromBlocks_cor_mul_fromBlocks_cor {R : Type} [CommRing R] {N : ℕ} (a b c d a' b' c' d' : R)
    (A B C D A' B' C' D' : Matrix (Fin N) (Fin N) R) :
    Matrix.fromBlocks (cor a A) (cor b B) (cor c C) (cor d D) *
        Matrix.fromBlocks (cor a' A') (cor b' B') (cor c' C') (cor d' D') =
      Matrix.fromBlocks (cor (a * a' + b * c') (A * A' + B * C')) (cor (a * b' + b * d') (A * B' + B * D'))
        (cor (c * a' + d * c') (C * A' + D * C')) (cor (c * b' + d * d') (C * B' + D * D')) := by
  rw [Matrix.fromBlocks_multiply]
  simp only [cor_mul, cor_add]

theorem emb_mem {γ : M2 E N} (h : γ ∈ UU E N) : emb γ ∈ UU E (N + 1) := by
  have h' : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  rw [← Matrix.fromBlocks_toBlocks γ, ccT_fromBlocks, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h'
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp h'
  have hJ : Matrix.J (Fin (N + 1)) E =
      Matrix.fromBlocks (cor 0 0) (cor (-1) (-1)) (cor 1 1) (cor 0 0) := by
    rw [Matrix.J, cor_zero, ← cor_neg, cor_one]
  show ccT (emb γ) * Matrix.J (Fin (N + 1)) E * emb γ = Matrix.J (Fin (N + 1)) E
  rw [hJ, emb, ccT_fromBlocks, ccT_cor, ccT_cor, ccT_cor, ccT_cor, fromBlocks_cor_mul_fromBlocks_cor, fromBlocks_cor_mul_fromBlocks_cor]
  simp only [h11, h12, h21, h22, cc, map_one, map_zero]
  congr 1 <;> congr 1 <;> ring

omit [NumberField E] [IsCMField E] in
theorem hDen_emb_det (γ : M2 E N) (Z : CM Ψ (N + 1) (N + 1)) (τ : Ψ) :
    (hDen Ψ (emb γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det := by
  simp only [hDen, emb, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one]
  exact det_cor_den _ _ _

def corZ (s : ℂ) (Z : CM Ψ N N) : CM Ψ (N + 1) (N + 1) := fun τ => cor s (Z τ)

def corV (z : CM Ψ n N) : CM Ψ n (N + 1) := fun τ => Matrix.of fun k => Fin.cons 0 (z τ k)

omit [NumberField E] [IsCMField E] in
theorem corZ_mem {Z : CM Ψ N N} (h : Z ∈ Hn Ψ N) : corZ I Z ∈ Hn Ψ (N + 1) := by
  intro τ
  show (imH (cor I (Z τ))).PosDef
  rw [imH_cor]
  exact posDef_cor_one _ (h τ)

omit [NumberField E] [IsCMField E] in
theorem pushZ_corZ (Z : CM Ψ N N) (t : ℝ) :
    pushZ Ψ (corZ I Z) (Pi.single 0 1) t = corZ (I + I * t) Z := by
  funext τ
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [pushZ, corZ, Matrix.vecMulVec_apply, Pi.single_apply, Fin.succ_ne_zero]

omit [NumberField E] [IsCMField E] in
theorem dropZ_corZ (s : ℂ) (Z : CM Ψ N N) : dropZ Ψ (corZ s Z) = Z := by
  funext τ
  ext i j
  simp [dropZ, corZ]

omit [NumberField E] [IsCMField E] in
theorem drop_corV (z : CM Ψ n N) : (fun τ => (corV z τ).submatrix id Fin.succ) = z := by
  funext τ
  ext k a
  simp [corV]

omit [NumberField E] [IsCMField E] in
theorem hDen_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen Ψ γ Z τ) := by
  simp only [hDen, emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, zero_mul, zero_add]

omit [NumberField E] [IsCMField E] in
theorem hDen'_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (τ : Ψ) :
    hDen' Ψ (emb γ) (corZ s Z) τ = cor 1 (hDen' Ψ γ Z τ) := by
  simp only [hDen', emb, corZ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, cor_map, map_zero, map_one,
    cor_conjTranspose, cor_mul, cor_add, mul_zero, zero_add, map_one]

omit [NumberField E] [IsCMField E] in
theorem hAct_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0) :
    hAct Ψ (emb γ) (corZ s Z) = corZ s (hAct Ψ γ Z) := by
  funext τ
  simp only [hAct]
  rw [hDen_emb, cor_inv _ (h τ)]
  simp only [emb, corZ, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, cor_map, map_zero, map_one,
    cor_mul, cor_add, one_mul, add_zero, mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
theorem hFac_emb (γ : M2 E N) (s : ℂ) (Z : CM Ψ N N) (h : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0)
    (z z' : CM Ψ n N) : hFac Ψ (emb γ) (corZ s Z) (corV z) (corV z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hDen_emb, det_cor_one, cor_inv _ (h τ)]
  simp only [emb, Matrix.toBlocks_fromBlocks₂₁, cor_map, map_zero, cor_mul, one_mul]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  show (Fin.cons 0 (z' τ k) : Fin (N + 1) → ℂ) ⬝ᵥ cor 0 _ *ᵥ (Fin.cons 0 (z τ k) : Fin (N + 1) → ℂ) = _
  rw [cor_mulVec, cons_dot]
  simp

theorem transH_drop (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    (h : TransH Ψ (emb γ) φ ψ) : TransH Ψ γ (dropF φ) (dropF ψ) := by
  intro Z hZ z z'
  obtain ⟨hden, hact, -⟩ := (GlobalTheory.T.unitary_act_halfSpace_alt E Ψ N γ hγ).2 Z hZ
  have hdet : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hden τ).1
  have hdet' : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h0 =>
    (hden τ).1 (by rw [← (hden τ).2.1, h0, zero_mul])
  obtain ⟨w, hw⟩ : ∃ w : CM Ψ n N, w = fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : CM Ψ n N, w' = fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hw, ← hw']
  have hWφ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).2 (corZ I Z) (corZ_mem hZ)
  have hWψ := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N ψ hψ).2 (corZ I (hAct Ψ γ Z)) (corZ_mem hact)
  have L1 := hWφ.2.2 (corV z) (corV z')
  have L2 := hWψ.2.2 (corV w) (corV w')
  simp only [dropZ_corZ, drop_corV] at L1 L2
  have key : ∀ t : ℝ, 0 ≤ t →
      thH Ψ ψ (pushZ Ψ (corZ I (hAct Ψ γ Z)) (Pi.single 0 1) t) (corV w) (corV w') =
        hFac Ψ γ Z z z' * thH Ψ φ (pushZ Ψ (corZ I Z) (Pi.single 0 1) t) (corV z) (corV z') := by
    intro t ht
    have hmem := hWφ.2.1 t ht
    have e := h _ hmem (corV z) (corV z')
    simp only [pushZ_corZ] at hmem e ⊢
    rw [hAct_emb γ _ Z hdet, hFac_emb γ _ Z hdet] at e
    rw [← e]
    congr 1
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw, corV, hDen'_emb, cor_inv _ (hdet' τ), Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · funext τ
      ext k j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [hw', corV, hDen_emb, cor_inv _ (hdet τ), Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  exact tendsto_nhds_unique_of_eventuallyEq L2 (L1.const_mul _) ((Filter.eventually_ge_atTop 0).mono key)

theorem dropF_weil (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ} (hφ : IsSB φ) :
    dropF (weil Ψ (emb γ) φ) = weil Ψ γ (dropF φ) := by
  obtain ⟨hsb, htr, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n (N + 1) hn (emb γ) (emb_mem hγ) φ hφ
  have hd := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N φ hφ).1
  have hdw := (GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ hsb).1
  exact (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ (dropF φ) hd).2.2.1 _ hdw (transH_drop hΨ hγ hφ hsb htr)

abbrev up (N : ℕ) : Fin N ⊕ Fin N → Fin (N + 1) ⊕ Fin (N + 1) := Sum.map Fin.succ Fin.succ

def extV (E : Type) [Field E] (N : ℕ) :
    (Fin N ⊕ Fin N → E) →ₗ[E] (Fin (N + 1) ⊕ Fin (N + 1) → E) where
  toFun v := Sum.elim (Fin.cons 0 fun a => v (Sum.inl a)) (Fin.cons 0 fun a => v (Sum.inr a))
  map_add' v w := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c v := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp

omit [IsCMField E] in

theorem botSpan_eq (h : M2 E (N + 1)) (h0 : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1)
    (h1 : ∀ a, h (Sum.inr a) (Sum.inl 0) = 0) :
    botSpan h = (E ∙ Pi.single (Sum.inr 0) 1) ⊔
      (botSpan (h.submatrix (up N) (up N))).map (extV E N) := by
  have key : ∀ b : Fin N, extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) =
      h (Sum.inr b.succ) - h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 := by
    intro b
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp [extV, h1, Pi.single_apply]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    show h (Sum.inr a) ∈ _
    induction a using Fin.cases with
    | zero => rw [h0]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    | succ b =>
      have e : h (Sum.inr b.succ) = h (Sum.inr b.succ) (Sum.inr 0) • Pi.single (Sum.inr 0) 1 +
          extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) := by rw [key]; abel
      rw [e]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, rfl⟩)))
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem, ← h0]
      exact Submodule.subset_span ⟨0, rfl⟩
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, rfl⟩
      show extV E N ((h.submatrix (up N) (up N)) (Sum.inr b)) ∈ botSpan h
      rw [key]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨b.succ, rfl⟩) (Submodule.smul_mem _ _ ?_)
      rw [← h0]
      exact Submodule.subset_span ⟨0, rfl⟩

omit [IsCMField E] in
theorem botSpan_emb (γ : M2 E N) :
    botSpan (emb γ) = (E ∙ Pi.single (Sum.inr 0) 1) ⊔ (botSpan γ).map (extV E N) := by
  have h0 : emb γ (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    ext (j | j) <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [emb, Pi.single_apply]
  have h1 : ∀ a, emb γ (Sum.inr a) (Sum.inl 0) = 0 := by
    intro a; refine Fin.cases ?_ (fun a => ?_) a <;> simp [emb]
  have hs : (emb γ).submatrix (up N) (up N) = γ := by
    ext (i | i) (j | j) <;>
      simp [emb, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
  rw [botSpan_eq (emb γ) h0 h1, hs]

omit [IsCMField E] in
theorem map_botSpan_emb (γ : M2 E N) :
    (botSpan (emb γ)).map (LinearMap.funLeft E E (up N)) = botSpan γ := by
  rw [botSpan_emb, Submodule.map_sup, Submodule.map_span, Set.image_singleton, ← Submodule.map_comp]
  have e1 : LinearMap.funLeft E E (up N) (Pi.single (Sum.inr 0) 1) = 0 := by
    funext j
    rcases j with j | j <;> simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.succ_ne_zero]
  have e2 : (LinearMap.funLeft E E (up N)).comp (extV E N) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    funext j
    rcases j with j | j <;> simp [extV, LinearMap.funLeft_apply]
  rw [e1, e2, Submodule.map_id, Submodule.span_singleton_eq_bot.mpr rfl, bot_sup_eq]

omit [IsCMField E] in
theorem botSpan_emb_iff (γ γ' : M2 E N) :
    botSpan (emb γ) = botSpan (emb γ') ↔ botSpan γ = botSpan γ' := by
  constructor
  · intro h
    rw [← map_botSpan_emb γ, h, map_botSpan_emb]
  · intro h
    rw [botSpan_emb, botSpan_emb, h]

omit [IsCMField E] in
theorem botSpan_mul_le {m : ℕ} (a d : Matrix (Fin m) (Fin m) E) (g : M2 E m) :
    botSpan (Matrix.fromBlocks a 0 0 d * g) ≤ botSpan g := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have e : (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) = ∑ k, d i k • g (Sum.inr k) := by
    ext j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply]
  show (Matrix.fromBlocks a 0 0 d * g) (Sum.inr i) ∈ botSpan g
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

omit [NumberField E] [IsCMField E] in

theorem exists_col (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, IsUnit b.det ∧ ∀ i, b i 0 = v i := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc
    exact hv (funext fun i => by_contra fun hi => hc ⟨i, hi⟩)
  set c : Matrix (Fin (N + 1)) (Fin (N + 1)) E := Matrix.of fun i j =>
    Fin.cases (v (Equiv.swap 0 k i)) (fun j' : Fin N => if i = j'.succ then (1 : E) else 0) j with hcdef
  have hc : c.det = v k := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have e : c.submatrix Fin.succ (Fin.succAbove 0) = 1 := by
      ext i j
      simp [hcdef, Matrix.one_apply]
    rw [e]
    simp [hcdef, Fin.succ_ne_zero, eq_comm (a := (0 : Fin (N + 1)))]
  refine ⟨c.submatrix (Equiv.swap 0 k) id, ?_, fun i => ?_⟩
  · rw [Matrix.det_permute, hc]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ hk)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 k)) with hs | hs <;> simp [hs]
  · simp [hcdef]

private theorem ccT_mul_J_mul_apply {m : ℕ} (M : M2 E m) (p q : Fin m ⊕ Fin m) :
    (ccT M * Matrix.J (Fin m) E * M) p q =
      ∑ i, cc (M (Sum.inr i) p) * M (Sum.inl i) q - ∑ i, cc (M (Sum.inl i) p) * M (Sum.inr i) q := by
  simp [Matrix.mul_apply, Matrix.J, ccT, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

private theorem cc_cc_siegel_theta_transformation (x : E) : cc (cc x) = x := by
  have := congrFun (congrFun (Base.ccT_ccT (Matrix.of fun (_ : Unit) (_ : Unit) => x)) ()) ()
  simpa [ccT] using this

theorem sub_mem {h : M2 E (N + 1)} (hh : h ∈ UU E (N + 1))
    (hc : ∀ i, h i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) i) :
    h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 ∧ h.submatrix (up N) (up N) ∈ UU E N := by
  have hU : ∀ p q, (ccT h * Matrix.J (Fin (N + 1)) E * h) p q = Matrix.J (Fin (N + 1)) E p q := by
    intro p q
    rw [show ccT h * Matrix.J (Fin (N + 1)) E * h = Matrix.J (Fin (N + 1)) E from hh]
  have hl : ∀ i, h (Sum.inl i) (Sum.inl 0) = if i = 0 then 1 else 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hr : ∀ i, h (Sum.inr i) (Sum.inl 0) = 0 := fun i => by
    rw [hc]; simp [Pi.single_apply]
  have hrow : h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 := by
    funext p
    have e := hU p (Sum.inl 0)
    rw [ccT_mul_J_mul_apply] at e
    simp only [hl, hr, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    have e2 : Matrix.J (Fin (N + 1)) E p (Sum.inl 0) = (Pi.single (Sum.inr 0) 1 : _ → E) p := by
      rcases p with p | p <;> simp [Matrix.J, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e2] at e
    have e3 := congrArg cc e
    rw [cc_cc_siegel_theta_transformation] at e3
    rw [e3]
    rcases p with p | p <;> simp [Pi.single_apply, cc]
  refine ⟨hrow, ?_⟩
  have hJ : ∀ p q, Matrix.J (Fin (N + 1)) E (up N p) (up N q) = Matrix.J (Fin N) E p q := by
    rintro (p | p) (q | q) <;> simp [Matrix.J, Matrix.one_apply]
  have z1 : ∀ x : Fin N ⊕ Fin N, (Pi.single (Sum.inr 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) (up N x) = 0 := by
    rintro (x | x) <;> simp [Pi.single_apply, Fin.succ_ne_zero]
  show ccT (h.submatrix (up N) (up N)) * Matrix.J (Fin N) E * h.submatrix (up N) (up N) = Matrix.J (Fin N) E
  ext p q
  have e := hU (up N p) (up N q)
  rw [ccT_mul_J_mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, hrow, hJ] at e
  rw [ccT_mul_J_mul_apply, ← e]
  simp [z1, cc]

theorem exists_botSpan {g : M2 E (N + 1)} (hg : g ∈ UU E (N + 1))
    (h0 : ∀ a, g.toBlocks₂₁ a 0 = 0) : ∃ γ ∈ UU E N, botSpan g = botSpan (emb γ) := by
  have hgU := (GlobalTheory.T.unitary_act_halfSpace_alt E (∅ : Finset (E →+* ℂ)) (N + 1) g hg).1
  have h0' : ∀ a, g (Sum.inr a) (Sum.inl 0) = 0 := fun a => by simpa [Matrix.toBlocks₂₁] using h0 a
  obtain ⟨v, hvd⟩ : ∃ v : Fin (N + 1) → E, v = fun i => g (Sum.inl i) (Sum.inl 0) := ⟨_, rfl⟩
  have hv : v ≠ 0 := by
    intro hv0
    refine (isUnit_iff_ne_zero.mp hgU.1) (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) ?_)
    rintro (i | i)
    · have := congrFun hv0 i
      rw [hvd] at this
      simpa using this
    · exact h0' i
  obtain ⟨b, hb, hbv⟩ := exists_col v hv
  have e2 : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv _ hb
  have e1 : ccT b⁻¹ * ccT b = 1 := by rw [← Base.ccT_mul, e2, Base.ccT_one]
  have e0 : ccT (0 : Matrix (Fin (N + 1)) (Fin (N + 1)) E) = 0 := by
    ext i j; simp [ccT, cc]
  obtain ⟨δ, hδd⟩ : ∃ δ : M2 E (N + 1), δ = Matrix.fromBlocks b⁻¹ 0 0 (ccT b) := ⟨_, rfl⟩
  have hδ : δ ∈ UU E (N + 1) := by
    show ccT δ * Matrix.J _ E * δ = Matrix.J _ E
    rw [hδd, ccT_fromBlocks, e0, Base.ccT_ccT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [e1, e2]
  have hh : δ * g ∈ UU E (N + 1) := hgU.2.2.2.2 δ hδ
  have hv' : b *ᵥ Pi.single 0 1 = v := by
    funext i; simp [Matrix.mulVec_single, hbv]
  have hinv : b⁻¹ *ᵥ v = Pi.single 0 1 := by
    rw [← hv', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]
  have hc : ∀ i, (δ * g) i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : _ → E) i := by
    rintro (i | i)
    · have := congrFun hinv i
      rw [hvd] at this
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0', this, Pi.single_apply]
    · simp [hδd, Matrix.mul_apply, Fintype.sum_sum_type, h0']
  obtain ⟨hrow, hsub⟩ := sub_mem hh hc
  have h1 : ∀ a, (δ * g) (Sum.inr a) (Sum.inl 0) = 0 := fun a => by rw [hc]; simp
  refine ⟨(δ * g).submatrix (up N) (up N), hsub, ?_⟩
  rw [botSpan_emb, ← botSpan_eq (δ * g) hrow h1]
  apply le_antisymm
  · calc botSpan g = botSpan (Matrix.fromBlocks b 0 0 (ccT b⁻¹) * (δ * g)) := by
          rw [← Matrix.mul_assoc, hδd, Matrix.fromBlocks_multiply]
          simp [e1, e2]
      _ ≤ botSpan (δ * g) := botSpan_mul_le _ _ _
  · rw [hδd]
    exact botSpan_mul_le _ _ _

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  intro E _ _ _ Ψ hΨ n N hn
  refine ⟨emb, fun γ hγ => ⟨emb_mem hγ, fun a => ?_, fun Z τ => hDen_emb_det γ Z τ,
    fun φ hφ => dropF_weil hΨ hn hγ hφ, fun γ' _ => botSpan_emb_iff γ γ'⟩, fun g hg h0 => exists_botSpan hg h0⟩
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [emb]

end

end GlobalTheory.SW.Emb
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_compatible_with_weil_and_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  atlas_forward_decl GlobalTheory.SW.Emb.exists_embedding
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.EisSiegel

variable {N : ℕ}

theorem det_growth (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : D * Cᴴ = C * Dᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ (C *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ, ‖(C * Z + D).det‖ * (1 + t * c) ≤
      ‖(C * (Z + (I * t) • vecMulVec v (star v)) + D).det‖ := by
  have hH : (C * Dᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h]
  set Q := C * Z + D with hQdef
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  set x : Fin N → ℂ := (Q⁻¹)ᴴ *ᵥ v with hx
  have hxv : Qᴴ *ᵥ x = v := by
    rw [hx, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hU, conjTranspose_one, one_mulVec]
  have hsx : star x = star v ᵥ* Q⁻¹ := by
    rw [hx, star_mulVec, conjTranspose_conjTranspose]
  have hs := im_quad_denom C D Z hH x
  rw [← hQdef, hxv] at hs
  refine ⟨(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re,
    (Complex.nonneg_iff.1 (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ x))).1,
    fun hv => (Complex.pos_iff.1 (hZ.dotProduct_mulVec_pos fun h0 => hv ?_)).1, fun t => ?_⟩
  · rw [← hxv, hQdef, conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec x Zᴴ, h0,
      mulVec_zero, zero_add, mulVec_mulVec, ← h, ← mulVec_mulVec, h0, mulVec_zero]
  · have e : C * (Z + (I * t) • vecMulVec v (star v)) + D =
        Q * (1 + vecMulVec ((I * t) • (Q⁻¹ *ᵥ (C *ᵥ v))) (star v)) := by
      rw [Matrix.mul_add Q, Matrix.mul_one, mul_vecMulVec, mulVec_smul, mulVec_mulVec,
        mul_nonsing_inv _ hU, one_mulVec, Matrix.mul_add, ← smul_vecMulVec, mul_vecMulVec,
        mulVec_smul, hQdef]
      abel
    rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, norm_mul,
      dotProduct_smul, dotProduct_mulVec (star v), ← hsx]
    generalize (star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re = c at hs
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (Complex.re_le_norm _)) (norm_nonneg _)
    simp only [smul_eq_mul, add_re, one_re, mul_re, mul_im, I_re, I_im, zero_mul, one_mul,
      ofReal_re, ofReal_im, hs]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}

omit [NumberField E] [IsCMField E] in

theorem pushZ_mem {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have hP : ((t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have := imH_add_I_smul (Z τ) _ hP.1
  rw [smul_smul] at this
  exact this ▸ (hZ τ).add_posSemidef hP

omit [NumberField E] [IsCMField E] in
theorem dropZ_pushZ (Z : CM Ψ (N + 1) (N + 1)) (t : ℝ) :
    dropZ Ψ (pushZ Ψ Z (Pi.single 0 1) t) = dropZ Ψ Z := by
  funext τ
  ext a b
  simp [dropZ, pushZ, vecMulVec_apply]

theorem hDen_growth {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (τ : Ψ) :
    (hDen Ψ γ Z τ).det ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ (γ.toBlocks₂₁ *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ,
      ‖(hDen Ψ γ Z τ).det‖ * (1 + t * c) ≤ ‖(hDen Ψ γ (pushZ Ψ Z v t) τ).det‖ := by
  have h0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  obtain ⟨c, h1, h2, h3⟩ := det_growth _ _ _ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2 h0
    (hZ τ) (fun a => τ.1 (v a))
  refine ⟨h0, c, h1, fun hv => h2 fun h => hv ?_, h3⟩
  funext a
  apply τ.1.injective
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  exact congrFun h a

theorem norm_term_le {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (φ : Matrix (Fin n) (Fin N) E → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0‖ ≤ ‖eisTerm Ψ γ φ Z 0 0‖ := by
  simp only [eisTerm, EisTrans.hFac_zero, norm_mul, norm_inv, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ ?_ ?_) (norm_nonneg _)
  · exact Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hDen_growth Ψ hγ hZ v τ).1) _
  · refine Finset.prod_le_prod (fun _ _ => by positivity) fun τ _ => ?_
    obtain ⟨-, c, h1, -, h3⟩ := hDen_growth Ψ hγ hZ v τ
    refine pow_le_pow_left₀ (norm_nonneg _) (le_trans ?_ (h3 t)) _
    exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [mul_nonneg ht h1])

theorem term_tendsto_zero (hΨ : IsType Ψ) (hn : n ≠ 0) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) (hv : γ.toBlocks₂₁ *ᵥ v ≠ 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Tendsto (fun t : ℝ => eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  have hne : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩⟩
    · exact ⟨⟨_, not_not.1 ((hΨ σ).not.1 h)⟩⟩
  simp only [eisTerm, EisTrans.hFac_zero, ← Finset.prod_inv_distrib]
  have h1 : ∀ τ : Ψ, Tendsto (fun t : ℝ => ((hDen Ψ γ (pushZ Ψ Z v t) τ).det ^ n)⁻¹) atTop
      (𝓝 0) := by
    intro τ
    obtain ⟨h0, c, -, h2, h3⟩ := hDen_growth Ψ hγ hZ v τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv, norm_pow]
    refine Tendsto.inv_tendsto_atTop ((tendsto_pow_atTop hn).comp (tendsto_atTop_mono h3 ?_))
    exact Tendsto.const_mul_atTop (norm_pos_iff.2 h0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const (h2 hv)))
  have h2 := (tendsto_finset_prod Finset.univ fun τ _ => h1 τ).const_mul (weil Ψ γ φ 0)
  rwa [Finset.prod_const, zero_pow (Finset.card_univ.trans_ne Fintype.card_ne_zero), mul_zero] at h2

end GlobalTheory.SW.EisSiegel

open GlobalTheory.SW.EisSiegel in

theorem GlobalTheory.SW.eis_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  intro E _ _ _ Ψ hΨ n N hn hN φ hφ Z hZ
  obtain ⟨ι, hι, hsurj⟩ := GlobalTheory.T.embedding_compatible_with_weil_and_denominator E Ψ hΨ n N hn
  let j : Lag E N → Lag E (N + 1) := fun V =>
    ⟨botSpan (ι V.2.choose), _, (hι _ V.2.choose_spec.1).1, rfl⟩
  have hj : Function.Injective j := fun V W h => Subtype.ext (by
    rw [← V.2.choose_spec.2, ← W.2.choose_spec.2]
    exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ W.2.choose_spec.1).1 (congrArg Subtype.val h))
  unfold eis
  rw [← tsum_extend_zero hj]
  refine tendsto_tsum_of_dominated_convergence
    ((eis_automorphy_linear E Ψ hΨ n (N + 1) hn hN φ hφ Z hZ).1 0 0) (fun U => ?_) ?_
  · by_cases hU : ∃ V, j V = U
    · obtain ⟨V, rfl⟩ := hU
      rw [hj.extend_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨a1, -, a3, a4, -⟩ := hι _ V.2.choose_spec.1
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n (N + 1) hn φ hφ).2 _ (j V).2.choose_spec.1 _ a1
        (j V).2.choose_spec.2 _ (pushZ_mem Ψ hZ _ ht)]
      simp only [eisTerm, EisTrans.hFac_zero, a3, dropZ_pushZ]
      rw [← a4 φ hφ, dropF]
      congr 2
      ext k a
      refine Fin.cases rfl (fun _ => rfl) a
    · rw [Function.extend_apply' _ _ _ hU]
      refine term_tendsto_zero Ψ hΨ (by omega) U.2.choose_spec.1 hZ _ (fun h0 => hU ?_) φ
      obtain ⟨γ, hγ, e⟩ := hsurj _ U.2.choose_spec.1 fun a => by
        simpa using congrFun h0 a
      let V : Lag E N := ⟨botSpan γ, γ, hγ, rfl⟩
      refine ⟨V, Subtype.ext ?_⟩
      rw [← U.2.choose_spec.2, e]
      exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ hγ).2 V.2.choose_spec.2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht U
    exact norm_term_le Ψ U.2.choose_spec.1 hZ _ φ ht
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelOperator_hermitianEisensteinSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  atlas_forward_decl GlobalTheory.SW.eis_siegel_operator
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}

omit [IsCMField E] in

theorem exists_den {α β : Type} [Fintype α] [Fintype β] (γ : Matrix α β E) :
    ∃ c : ℕ, 0 < c ∧ Den c γ := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : α × β => γ p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun i j => ?_⟩
  have h := hy (γ i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul, Nat.cast_natAbs]
  rw [zsmul_eq_mul] at h
  rcases abs_choice y with e | e
  · rw [e]; exact h
  · rw [e, Int.cast_neg, neg_mul]; exact h.neg

omit [NumberField E] [IsCMField E] in

theorem exists_inv (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ a b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, b * a = 1 ∧ a *ᵥ v = Pi.single 0 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let b : Matrix (Fin (N + 1)) (Fin (N + 1)) E :=
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)
  have hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hb : IsUnit b.det := by
    rw [Matrix.det_permute', hd]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)
    exact (Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)
  have hbv : b *ᵥ Pi.single 0 1 = v := by
    ext k; simp [b]
  refine ⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩
  rw [← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]

omit [NumberField E] [IsCMField E] in

theorem pushZ_mem (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext i j
    simp [imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]
    field_simp
    linear_combination (-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq
  rw [e]
  exact (hZ τ).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))

theorem levi_mem {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1) :
    (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) ∈ UU E N := by
  have e : ccT (Matrix.fromBlocks a 0 0 (ccT b) : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 b := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  have h' : ccT a * ccT b = 1 := by rw [← Base.ccT_mul, h, Base.ccT_one]
  change ccT _ * _ * _ = _
  rw [e]
  simp [Matrix.J, Matrix.fromBlocks_multiply, h, h']

theorem hAct_levi (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (τ : Ψ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z τ = a.map τ.1 * Z τ * (a.map τ.1)ᴴ := by
  have h1 : b.map τ.1 * a.map τ.1 = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((b.map τ.1)ᴴ)⁻¹ = (a.map τ.1)ᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp [hAct, hDen, Base.ccT_map, h2]

theorem hAct_pushZ (Ψ : Finset (E →+* ℂ)) {a b : Matrix (Fin N) (Fin N) E} (h : b * a = 1)
    (Z : CM Ψ N N) (v : Fin N → E) (t : ℝ) :
    hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) (pushZ Ψ Z v t) =
      pushZ Ψ (hAct Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z) (a *ᵥ v) t := by
  funext τ
  unfold pushZ
  rw [hAct_levi Ψ h, hAct_levi Ψ h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 3
  · funext i; simp [Matrix.mulVec, dotProduct]
  · funext i; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]

theorem hFac_levi (Ψ : Finset (E →+* ℂ)) (a b : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) :
    hFac Ψ (Matrix.fromBlocks a 0 0 (ccT b)) Z (0 : CM Ψ n N) 0 =
      ∏ τ : Ψ, ((ccT b).map τ.1).det ^ n := by
  simp [hFac, hDen]

omit [IsCMField E] in

theorem colsIn_cons (Λ : Lt E n) (c : E) (x : Matrix (Fin n) (Fin N) E) :
    ColsIn Λ (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E)) ↔
      ColsIn Λ (c • x) := by
  unfold ColsIn
  rw [Fin.forall_fin_succ]
  have : (c • (Matrix.of fun k => Fin.cons 0 (x k) : Matrix (Fin n) (Fin (N + 1)) E))ᵀ 0 = 0 := by
    ext k; simp
  rw [this]
  exact ⟨fun h => h.2, fun h => ⟨Λ.zero_mem, h⟩⟩

theorem admissibleLatticeFamily_restrictFirstColumnZero {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ) :
    admitted M R (fun Λ => dropF (φ Λ)) := by
  refine ⟨hφ.pos, ?_, ?_, ?_, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' m x
    unfold dropF
    rw [← hφ.equiv h hh Λ hΛ Λ' hΛ' m]
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.mul_apply]
  · intro Λ hΛ x hx
    exact (colsIn_cons Λ _ x).1 (hφ.supp Λ hΛ _ hx)
  · intro Λ hΛ x y hy
    have hy' := (colsIn_cons Λ 1 y).2 (by rwa [one_smul])
    rw [one_smul] at hy'
    unfold dropF
    rw [← hφ.per Λ hΛ (Matrix.of fun k => Fin.cons 0 (x k)) _ hy']
    congr 1
    ext k j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  · intro Λ hΛ Λ' hΛ' ha x hx hx'
    exact hφ.loc Λ hΛ Λ' hΛ' ha _ ((colsIn_cons Λ _ x).2 hx) ((colsIn_cons Λ' _ x).2 hx')

theorem isSB_of_adm {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ}
    {φ : Fam E n N} (hφ : admitted M R φ) : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := by
  intro Λ hΛ
  obtain ⟨c, hc, hd⟩ := exists_den (1 : M2 E N)
  obtain ⟨_, _, -, h⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hφ.pos.2
  exact (h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1

theorem tendsto_first {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n)
    (hN : 4 * (N + 1) < n) (hsw : SWAt Ψ n N) {M R : ℕ} {φ : Fam E n (N + 1)} (hφ : admitted M R φ)
    {Z : CM Ψ (N + 1) (N + 1)} (hZ : Z ∈ Hn Ψ (N + 1)) :
    Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 0) := by
  have hsb := isSB_of_adm hΨ hn hφ
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hφ.pos.1).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hZ' : dropZ Ψ Z ∈ Hn Ψ N := ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N 0 isSB_zero).2 Z hZ).1
  rw [← hsw M R _ (admissibleLatticeFamily_restrictFirstColumnZero hφ) _ hZ']
  unfold swd classSum
  simp only [finsum_eq_sum_of_fintype]
  refine tendsto_finset_sum _ fun c _ => Tendsto.const_mul _ (Tendsto.sub ?_ ?_)
  · exact ((GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF E Ψ hΨ n N _ (hsb _ (Quot.out c).2)).2 Z hZ).2.2 0 0
  · exact GlobalTheory.T.siegelOperator_hermitianEisensteinSeries E Ψ hΨ n N hn hN _ (hsb _ (Quot.out c).2) Z hZ

end GlobalTheory.SW.Cusp

open GlobalTheory.SW.Cusp in

theorem GlobalTheory.SW.swd_tendsto_zero_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  intro E _ _ _ Ψ hΨ n N hn hN hsw M R φ hφ v hv Z hZ
  obtain ⟨a, b, hba, hav⟩ := exists_inv v hv
  have hγ := levi_mem hba
  obtain ⟨c, hc, hd⟩ := exists_den (Matrix.fromBlocks a 0 0 (ccT b) : M2 E (N + 1))
  obtain ⟨R', hR'⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  have hact := (unitary_act_halfSpace E Ψ (N + 1) _ hγ).2 Z hZ
  have hlim := tendsto_first hΨ hn hN hsw (hR' M φ hφ _ hγ hd) hact.2.1
  have hne : (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    simpa [hDen] using (hact.1 τ).1
  have h2 := hlim.const_mul (∏ τ : Ψ, ((ccT b).map τ.1).det ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h3 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hφ.pos.1 (isSB_of_adm hΨ hn hφ) _
    (pushZ_mem Ψ hZ v ht)).1 _ hγ
  rw [hAct_pushZ Ψ hba, hav, hFac_levi] at h3
  rw [h3, inv_mul_cancel_left₀ hne]
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_swd_pushZ_atTop_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∀ v : Fin (N + 1) → E, v ≠ 0 → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => swd Ψ M φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  atlas_forward_decl GlobalTheory.SW.swd_tendsto_zero_at_cusps
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace InvBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem exists_int_sum_type (hΨ : IsType Ψ) {t : E} (ht : IsIntegral ℤ t) (hc : cc t = t) :
    ∃ k : ℤ, ∑ τ : Ψ, τ.1 (2 * t) = k := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E t) := Algebra.isIntegral_trace ht
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨k, ?_⟩
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := t)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ σ : E →+* ℂ, σ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom _ _) _ _ fun _ => rfl).symm
  have h4 : ∑ σ ∈ Ψᶜ, σ t = ∑ σ ∈ Ψ, σ t := by
    refine Finset.sum_bij' (fun σ _ => ComplexEmbedding.conjugate σ)
      (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      by_contra h
      exact (Finset.mem_compl.1 hσ) ((hΨ σ).2 h)
    · intro σ hσ
      exact Finset.mem_compl.2 ((hΨ σ).1 hσ)
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _
      have := Base.map_cc σ t
      rw [hc] at this
      simpa using this
  rw [h3, ← Finset.sum_add_sum_compl Ψ, h4, ← hk] at h2
  rw [Finset.sum_coe_sort Ψ (fun τ => τ (2 * t))]
  simp only [map_mul, map_ofNat, ← Finset.mul_sum]
  rw [two_mul, ← h2]
  simp

theorem chiH_eq_one (hΨ : IsType Ψ) (R : ℕ) {y : Matrix (Fin N) (Fin N) E} (hy : IntM y)
    (hc : ccT y = y) {x : Matrix (Fin n) (Fin N) E} (hx : IntM ((R : E) • x)) :
    chiH Ψ (((2 * R ^ 2 : ℕ) : E) • y) x = 1 := by
  set u := (R : E) • x with hu
  have e : (x * (((2 * R ^ 2 : ℕ) : E) • y) * ccT x).trace = 2 * (u * y * ccT u).trace := by
    have : ccT u = (R : E) • ccT x := by
      ext i j; simp [hu, ccT, cc]
    rw [this, hu]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    push_cast; ring
  have hi : IsIntegral ℤ (u * y * ccT u).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun b _ =>
      (IsIntegral.sum _ fun a _ => (hx k a).mul (hy a b)).mul (Base.isIntegral_cc (hx k b))
  have hr : cc (u * y * ccT u).trace = (u * y * ccT u).trace := by
    have h1 : ccT (u * y * ccT u) = u * y * ccT u := by
      rw [Base.ccT_mul, Base.ccT_mul, Base.ccT_ccT, hc, Matrix.mul_assoc]
    have h2 : ∀ w : Matrix (Fin n) (Fin n) E, cc w.trace = (ccT w).trace := fun w => by
      simp [Matrix.trace, ccT, cc]
    rw [h2, h1]
  obtain ⟨k, hk⟩ := exists_int_sum_type hΨ hi hr
  rw [chiH, e, hk, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem exists_common_level {M R : ℕ} (hM : 0 < M) (hR : 0 < R) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ φ : Fam E n N, admitted M R φ → ∀ c : Cls E n M,
      HasLevel R₀ (φ (Quot.out c).1) := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  choose s hs _ h1 h2 using fun c : Cls E n M => (Quot.out c).2.2.2
  refine ⟨(∏ c, s c) * R, Nat.mul_pos (Finset.prod_pos fun c _ => hs c) hR, fun φ hφ c => ?_⟩
  obtain ⟨m, hm⟩ : s c ∣ ∏ c, s c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  rw [hm]
  constructor
  · intro x hx k a
    have := Base.nat_smul_mem _ m (h1 c _ (hφ.supp _ (Quot.out c).2 x hx a))
    have := (Base.mem_stdL _).1 this k
    convert this using 1
    simp; ring
  · intro x y hy
    have := hφ.per _ (Quot.out c).2 x (((s c * m : ℕ) : E) • y) fun a => by
      have := Base.nat_smul_mem _ m (h2 c (yᵀ a) ((Base.mem_stdL _).2 fun k => hy k a))
      convert this using 1
      ext k; simp; ring
    rw [← this, smul_smul]
    congr 3
    push_cast; ring

omit [IsCMField E] in

theorem differentiableOn_of_isHeat {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) :
    DifferentiableOn ℂ (fun Z : CF Ψ N N => D Z 0 0) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} := by
  have g : Differentiable ℂ (fun Z : CF Ψ N N => ((Z, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N)) :=
    differentiable_id.prodMk (differentiable_const _)
  have := DifferentiableOn.comp (s := {Z : CF Ψ N N | (Z : CM Ψ N N) ∈ Hn Ψ N}) hD.1
    g.differentiableOn fun Z hZ => hZ
  exact this

theorem bound_high (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * (N + 1) < n) (hS : SWAt Ψ n N)
    (M R : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ (N + 1) δ,
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  obtain ⟨R₀, hR₀, hL⟩ := exists_common_level (E := E) (n := n) (N := N + 1) hM hR
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded E Ψ hΨ n (N + 1) hn hN R₀ (δ / 4) hR₀ (by positivity)
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.decay_of_vanishing_at_cusps' E Ψ hΨ (N + 1) (2 * R₀ ^ 2) δ ((n : ℝ) / 2) (Nat.succ_pos N)
    (by positivity) hδ (by positivity)
  obtain ⟨R', C', -, hsb⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn 1 R one_pos hR
  refine ⟨C₂ * ((∑ c : Cls E n M, ‖(wt M (Quot.out c).1 : ℂ)‖) * (2 * C₁)),
    fun φ hφ B hB Z hZ => ?_⟩
  have hSB : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := fun Λ hΛ =>
    (hsb M Λ hΛ 1 Base.one_mem_UU (fun i j => by
      by_cases h : i = j <;> simp [h, isIntegral_one, isIntegral_zero])
      (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1
  rw [mul_assoc]
  refine hC₂ (fun Z => swd Ψ M φ Z 0 0) _ ?_ ?_ ?_ ?_ Z hZ
  · exact differentiableOn_of_isHeat (GlobalTheory.T.isHeat_swd_of_adm E Ψ hΨ n (N + 1) hn hN M R φ hφ)
  · intro y hy hc W hW
    have h := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM hSB W hW).2.1
      (((2 * R₀ ^ 2 : ℕ) : E) • y) (by
        conv_rhs => rw [← hc]
        ext i j; simp [ccT, cc])
    change swd Ψ M φ _ 0 0 = swd Ψ M φ W 0 0
    rw [← h]
    unfold swd classSum
    refine finsum_congr fun c => ?_
    have : (fun x => chiH Ψ (((2 * R₀ ^ 2 : ℕ) : E) • y) x * φ (Quot.out c).1 x) =
        φ (Quot.out c).1 := by
      funext x
      by_cases hx : φ (Quot.out c).1 x = 0
      · rw [hx, mul_zero]
      · rw [chiH_eq_one hΨ R₀ hy hc ((hL φ hφ c).1 x hx), one_mul]
    simp only [this]
  · intro W hW
    unfold swd classSum
    rw [finsum_eq_sum_of_fintype, mul_assoc, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨-, h1, h2⟩ := hC₁ _ (hL φ hφ c) B (hB _ (Quot.out c).2) W hW
    refine (norm_sub_le _ _).trans ?_
    linarith
  · exact GlobalTheory.T.tendsto_swd_pushZ_atTop_zero E Ψ hΨ n N hn hN hS M R φ hφ

theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.le_def.1 (hZ τ).det_pos.le).1

end InvBound

theorem swd_invariant_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N →
    ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1),
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn hN hS M R
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  obtain ⟨c, δ, hc, hδ, hred⟩ := GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high E Ψ hΨ (N + 1)
  obtain ⟨R', hadm⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  obtain ⟨R'', C₁, -, hlev⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn c R hc hR
  obtain ⟨C₂, hC₂⟩ := InvBound.bound_high hΨ hn hN hS M R' hδ
  refine ⟨C₂ * C₁, fun φ hφ B hB Z hZ => ?_⟩
  obtain ⟨γ, hγ, hd, hW⟩ := hred Z hZ
  have hl := fun Λ hΛ => hlev M Λ hΛ γ hγ hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩
  have h := hC₂ _ (hadm M φ hφ γ hγ hd) (C₁ * B) (fun Λ hΛ => (hl Λ hΛ).2.2 B (hB Λ hΛ)) _ hW
  rw [(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM (fun Λ hΛ => (hl Λ hΛ).1) Z hZ).1 γ hγ] at h
  obtain ⟨-, hH, hdet, -⟩ := (unitary_act_halfSpace E Ψ (N + 1) γ hγ).2 Z hZ
  have hf : ‖hFac Ψ γ Z (0 : CM Ψ n (N + 1)) 0‖ =
      (∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2) ^ ((n : ℝ) / 2) := by
    have h0 : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n (N + 1)) τ k = 0 := fun _ _ => rfl
    rw [← Real.finset_prod_rpow _ _ fun _ _ => by positivity]
    simp only [hFac, h0, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, norm_prod, norm_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast; ring
  rw [← hdet, Real.mul_rpow (InvBound.detIm_nonneg hH) (Finset.prod_nonneg fun _ _ => by positivity),
    ← hf, mul_assoc C₂]
  rw [norm_mul] at h
  refine le_of_eq_of_le ?_ h
  ring

end GlobalTheory.SW
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ, (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1), ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  atlas_forward_decl GlobalTheory.SW.swd_invariant_bound
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistAdm

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

def imL (b : Matrix (Fin N) (Fin N) E) : AddSubgroup (Fin N → E) :=
  (stdL E N).toAddSubgroup.map (Matrix.toLin' b).toAddMonoidHom

theorem mem_imL {b : Matrix (Fin N) (Fin N) E} {x : Fin N → E} :
    x ∈ imL b ↔ ∃ v ∈ stdL E N, b *ᵥ v = x := by
  simp [imL]

theorem std_eq_closure : (stdL E N).toAddSubgroup =
    AddSubgroup.closure (Set.range (Pi.basis fun _ : Fin N => integralBasis E)) := by
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  ext x
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Base.mem_stdL,
    Module.Basis.mem_span_iff_repr_mem, Sigma.forall]
  refine forall_congr' fun a => ?_
  simp only [Pi.basis_repr]
  rw [← Module.Basis.mem_span_iff_repr_mem, mem_span_integralBasis]
  exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe⟩

theorem relIndex_imL {b₁ b₂ : Matrix (Fin N) (Fin N) E} (h₁ : b₁.det ≠ 0) (h₂ : b₂.det ≠ 0)
    (hle : imL b₁ ≤ imL b₂) :
    ((imL b₁).relIndex (imL b₂) : ℚ) * |Algebra.norm ℚ b₂.det| = |Algebra.norm ℚ b₁.det| := by
  let B := Pi.basis fun _ : Fin N => integralBasis E
  have key : ∀ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 → ∃ B' : Module.Basis _ ℚ (Fin N → E),
      imL b = AddSubgroup.closure (Set.range B') ∧ B.det B' = Algebra.norm ℚ b.det := by
    intro b hb
    have hd : LinearMap.det (Matrix.toLin' b) ≠ 0 := by rwa [LinearMap.det_toLin']
    refine ⟨B.map (((Matrix.toLin' b).equivOfDetNeZero hd).restrictScalars ℚ), ?_, ?_⟩
    · rw [imL, std_eq_closure, AddMonoidHom.map_closure, ← Set.range_comp]
      rfl
    · rw [← LinearMap.det_toLin', ← LinearMap.det_restrictScalars]
      have := B.det_comp ((Matrix.toLin' b).restrictScalars ℚ) B
      rw [B.det_self, mul_one] at this
      exact this
  obtain ⟨B₁, e₁, d₁⟩ := key b₁ h₁
  obtain ⟨B₂, e₂, d₂⟩ := key b₂ h₂
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hle B₁ B₂ e₁ e₂, ← d₁, ← d₂, ← abs_mul, mul_comm,
    Module.Basis.det_mul_det]

theorem gidx_mul_le {𝔛 : Lt E N} {t : ℕ} (ht : 0 < t) (h : ∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛)
    {b : Matrix (Fin N) (Fin N) E} (hb : b.det ≠ 0) (hX : 𝔛.toAddSubgroup ≤ imL b) :
    gidx 𝔛 * |(Algebra.norm ℚ b.det : ℝ)| ≤ 1 := by
  have hs : ((t : E) • (1 : Matrix (Fin N) (Fin N) E)).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 ht.ne')
  set s := (t : E) • (1 : Matrix (Fin N) (Fin N) E) with hsd
  have h1 : imL (1 : Matrix (Fin N) (Fin N) E) = (stdL E N).toAddSubgroup := by
    ext x; simp [mem_imL]
  have hKX : imL s ≤ 𝔛.toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using h v hv
  have hKL : imL s ≤ (stdL E N).toAddSubgroup := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := mem_imL.1 hx
    simpa [hsd, Matrix.smul_mulVec] using nat_smul_mem _ t hv
  have e1 := relIndex_imL hs hb (hKX.trans hX)
  have e2 := relIndex_imL hs (b₂ := 1) (by simp) (h1 ▸ hKL)
  rw [h1, Matrix.det_one, map_one, abs_one, mul_one] at e2
  have hn : 0 < |Algebra.norm ℚ s.det| := abs_pos.2 (Algebra.norm_ne_zero_iff.2 hs)
  have n1 : (imL s).relIndex (imL b) ≠ 0 := fun h0 => by
    rw [h0] at e1; simp at e1; exact hn.ne' (by simpa using e1.symm)
  have l1 := AddSubgroup.relIndex_le_of_le_right (H := imL s) hX n1
  have m1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_right : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  have m2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (le_inf hKL hKX)
    (inf_le_left : (stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup ≤ _)
  rw [AddSubgroup.inf_relIndex_right] at m1
  rw [AddSubgroup.inf_relIndex_left] at m2
  rw [← m1] at l1
  rw [← m2] at e2
  unfold gidx
  generalize (imL s).relIndex ((stdL E N).toAddSubgroup ⊓ 𝔛.toAddSubgroup) = k at *
  generalize (stdL E N).toAddSubgroup.relIndex 𝔛.toAddSubgroup = p at *
  generalize 𝔛.toAddSubgroup.relIndex (stdL E N).toAddSubgroup = q at *
  have hkq : (0 : ℚ) < (k * q : ℕ) := e2 ▸ hn
  have hk : 0 < k := Nat.pos_of_mul_pos_right (by exact_mod_cast hkq)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (by exact_mod_cast hkq)
  have l2 : ((k * p : ℕ) : ℚ) * |Algebra.norm ℚ b.det| ≤ (k * q : ℕ) := by
    rw [e2, ← e1]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast l1) (abs_nonneg _)
  have l3 : (p : ℚ) * |Algebra.norm ℚ b.det| ≤ q := by
    push_cast at l2
    rw [mul_assoc] at l2
    exact le_of_mul_le_mul_left l2 (by exact_mod_cast hk)
  rw [div_mul_eq_mul_div, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast l3

theorem exists_frame (E : Type) [Field E] [NumberField E] (N : ℕ) : ∃ c : ℕ, 0 < c ∧
    ∀ (𝔛 : Lt E N) (t : ℕ), 0 < t → (∀ v ∈ 𝔛, (t : E) • v ∈ stdL E N) →
      (∀ v ∈ stdL E N, (t : E) • v ∈ 𝔛) → ∃ b : Matrix (Fin N) (Fin N) E, b.det ≠ 0 ∧
        (∀ v ∈ stdL E N, b *ᵥ v ∈ 𝔛) ∧ ∀ u, b *ᵥ u ∈ 𝔛 → (c : E) • u ∈ stdL E N := by
  obtain ⟨C, hC⟩ := NearPrim.exists_reduce E
  obtain ⟨M, hM⟩ := NearPrim.exists_approx E
  refine ⟨M.factorial ^ N, pow_pos M.factorial_pos _, fun 𝔛 t ht h1 h2 => ?_⟩
  have ht0 : (t : E) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  let L : AddSubgroup (Fin N → E) :=
    { carrier := {s | (t : E) • s ∈ 𝔛}
      add_mem' := fun {s t} hs ht => by
        rw [Set.mem_setOf_eq, smul_add]; exact add_mem hs ht
      zero_mem' := by simp
      neg_mem' := fun {s} hs => by rw [Set.mem_setOf_eq, smul_neg]; exact neg_mem hs }
  have hO : ∀ s : Fin N → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs =>
    h2 s ((Base.mem_stdL s).2 hs)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs => by
    change (t : E) • y • s ∈ 𝔛
    rw [smul_comm]
    exact 𝔛.smul_mem (⟨y, hy⟩ : 𝓞 E) hs
  have hden : ∀ s ∈ L, ∀ i, IsIntegral ℤ (((t * t : ℤ) : E) * s i) := fun s hs i => by
    have := (Base.mem_stdL _).1 (h1 _ hs) i
    simpa [mul_assoc] using this
  choose a haL ha0 hai haC hmin using NearPrim.exists_rows L hO (t * t)
    (by positivity) hden C hC
  refine ⟨(t : E) • (Matrix.of a)ᵀ, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_transpose,
      Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact mul_ne_zero (pow_ne_zero _ ht0) (Finset.prod_ne_zero_iff.2 fun i _ => hai i)
  · exact colsIn_mulVec (fun j => haL j) hv
  · rw [Matrix.smul_mulVec, Matrix.mulVec_transpose] at hu
    exact (Base.mem_stdL _).2 (NearPrim.integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin N
      le_rfl u (fun j hj => absurd j.2 (not_lt.2 hj)) hu)

variable [IsCMField E]

theorem admissibleLatticeFamily_moved_by_rational_matrix {M R : ℕ} {φ : Fam E n N} {𝔛 : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) 𝔛 (stdL E N)) (a : Matrix (Fin N) (Fin N) E) {c : ℕ} (hc0 : 0 < c)
    (h1 : ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ stdL E N) :
    admitted M (R * c) (fun Λ (x : Matrix (Fin n) (Fin N) E) => twist R 𝔛 φ Λ
      (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by
  have hex := exists_mult hφ.pos.2 hA
  refine ⟨⟨hφ.pos.1, Nat.mul_pos hφ.pos.2 hc0⟩, ?_,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).1,
    fun Λ hΛ => (twist_level hφ hA a c h1 h2 hΛ).2, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨R', hR'⟩ := twist_adm hφ hA
    have := hR'.equiv h hh Λ hΛ Λ' hΛ' hm (x * a)
    rwa [← Matrix.mul_assoc] at this
  · intro Λ hΛ Λ' hΛ' ⟨u, hu, hc, h3, h4⟩ x hx hx'
    have hct : u.Coprime (c * c) := by
      have : u.Coprime c := hc.coprime_dvd_right ⟨R * M, by ring⟩
      exact this.mul_right this
    have key : ∀ A B : Lt E n, (∀ v ∈ A, (u : E) • v ∈ B) → ColsIn B (((R * c : ℕ) : E) • x) →
        (∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ A) → ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ B := by
      intro A B hAB hB h ξ hξ
      refine mem_of_coprime B hct (hAB _ (h ξ hξ)) ?_
      have := colsIn_mulVec hB (h2 ξ hξ)
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec] at this
      rw [smul_smul]
      convert this using 2
      push_cast; ring
    simp only [twist_eq φ hex]
    by_cases h : ∀ ξ ∈ 𝔛, (R : E) • ((x * a) *ᵥ ξ) ∈ Λ
    · have h' := key Λ Λ' h3 hx' h
      rw [if_pos h, if_pos h']
      exact hφ.loc Λ hΛ Λ' hΛ' ⟨u, hu, hc.coprime_dvd_right ⟨c, by ring⟩, h3, h4⟩ _
        (cols_of_cond hex.choose_spec.2 h) (cols_of_cond hex.choose_spec.2 h')
    · rw [if_neg h, if_neg (fun h' => h (key Λ' Λ h4 hx h'))]

end GlobalTheory.SW.TwistMove

open GlobalTheory.SW.TwistMove in

theorem GlobalTheory.SW.twist_move_adm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  intro E _ _ _ N
  obtain ⟨c, hc, H⟩ := exists_frame E N
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine ⟨c, |(Algebra.norm ℚ ((c : E) ^ N) : ℝ)|, hc, fun n M R φ 𝔛 hφ _ hA => ?_⟩
  obtain ⟨t, ht, -, h1, h2⟩ := id hA
  obtain ⟨b, hb, hb1, hb2⟩ := H 𝔛 t ht h1 h2
  have hu : IsUnit b.det := hb.isUnit
  have ha : b⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det b hu).ne_zero
  have k2 : ∀ ξ ∈ 𝔛, (c : E) • (b⁻¹ *ᵥ ξ) ∈ stdL E N := fun ξ hξ => hb2 _ (by
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec])
  refine ⟨b⁻¹, ha, ?_, admissibleLatticeFamily_moved_by_rational_matrix hφ hA b⁻¹ hc (fun v hv => ⟨b *ᵥ ((c : E) • v),
    hb1 _ (TwistAdm.nat_smul_mem _ c hv), by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]⟩) k2⟩
  have hd : ((c : E)⁻¹ • b).det * ((c : E) ^ N * b⁻¹.det) = 1 := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Fintype.card_fin, inv_pow]
    field_simp
  have hle := gidx_mul_le ht h2 (left_ne_zero_of_mul_eq_one hd) (fun ξ hξ => mem_imL.2
    ⟨_, k2 ξ hξ, by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]⟩)
  have hn := congrArg (fun z : E => |((Algebra.norm ℚ z : ℚ) : ℝ)|) hd
  simp only [map_mul, Rat.cast_mul, abs_mul, map_one, Rat.cast_one, abs_one] at hn
  have := mul_le_mul_of_nonneg_right hle (mul_nonneg
    (abs_nonneg (Algebra.norm ℚ ((c : E) ^ N) : ℝ)) (abs_nonneg (Algebra.norm ℚ b⁻¹.det : ℝ)))
  rwa [mul_assoc, hn, mul_one, one_mul] at this
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (n M R : ℕ) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∃ a : Matrix (Fin N) (Fin N) E, a.det ≠ 0 ∧ gidx 𝔛 ≤ C * |(Algebra.norm ℚ a.det : ℝ)| ∧ admitted M (R * c) (fun Λ x => twist R 𝔛 φ Λ (x * a)) := by
  atlas_forward_decl GlobalTheory.SW.twist_move_adm
end

section
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

theorem abs_norm_eq (h : IsType Ψ) (t : E) :
    |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ τ : Ψ, ‖τ.1 t‖ ^ 2 := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
  have h3 : ∏ σ : E →+* ℂ, σ t = ∏ σ : E →ₐ[ℚ] ℂ, σ t :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
  have h1 : |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ t‖ := by
    rw [← norm_prod, h3, ← h2, eq_ratCast, Complex.norm_ratCast]
  rw [h1, Finset.prod_coe_sort Ψ fun τ => ‖τ t‖ ^ 2, ← Finset.prod_mul_prod_compl Ψ,
    Finset.prod_pow, sq]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem isSB_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.per Λ hΛ x _ fun a => h2 _ ((Base.mem_stdL _).2 fun k => hy k a)

theorem bounded_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M h.pos.1).1
  have h1 : ∀ c : Cls E n M, ∃ B : ℝ, ∀ x, ‖φ (Quot.out c).1 x‖ ≤ B := fun c => by
    obtain ⟨S, hS, hl⟩ := isSB_of_adm h (Quot.out c).2
    exact (ip_self_nonneg_and_bounds E _ _ S _ hS hl).2.2.2.2.1
  choose b hb using h1
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun Λ hΛ x => ?_⟩
  set c : Cls E n M := Quot.mk _ ⟨Λ, hΛ⟩ with hc
  obtain ⟨g, hg, hm⟩ := (Base.cls_eq_iff ⟨Λ, hΛ⟩ (Quot.out c)).1 (Quot.out_eq c).symm
  rw [← h.equiv g hg Λ hΛ _ (Quot.out c).2 hm x]
  exact ((hb c _).trans (hB ⟨c, rfl⟩)).trans (le_max_left _ _)

theorem det_ccT (a : Matrix (Fin N) (Fin N) E) : (ccT a).det = cc a.det := by
  rw [ccT, Matrix.det_transpose]
  exact ((IsCMField.complexConj E).toRingEquiv.toRingHom.map_det a).symm

theorem diag_mem_UU {a d : Matrix (Fin N) (Fin N) E} (h : ccT a * d = 1) :
    Matrix.fromBlocks a 0 0 d ∈ UU E N := by
  have h' : ccT d * a = 1 := by
    have := congrArg ccT h
    rwa [Base.ccT_mul, Base.ccT_ccT, Base.ccT_one] at this
  have e : ccT (Matrix.fromBlocks a 0 0 d : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 (ccT d) := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h, h']

theorem exists_moved (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {φ : Fam E n N} (hφ : ∀ Λ ∈ Vset E n M, IsSB (φ Λ)) {a : Matrix (Fin N) (Fin N) E}
    (ha : a.det ≠ 0) (hψ : ∀ Λ ∈ Vset E n M, IsSB fun x => φ Λ (x * a))
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : ∃ Z' ∈ Hn Ψ N,
      swd Ψ M (fun Λ x => φ Λ (x * a)) Z' 0 0 = swd Ψ M φ Z 0 0 ∧
        detIm Z' = |((Algebra.norm ℚ a.det : ℚ) : ℝ)| * detIm Z := by
  have ha' : (ccT a).det ≠ 0 := by
    rw [det_ccT]; simpa [cc] using ha
  set d := (ccT a)⁻¹ with hd
  have had : ccT a * d = 1 := Matrix.mul_nonsing_inv _ ha'.isUnit
  have hdet : cc a.det * d.det = 1 := by rw [← det_ccT, ← Matrix.det_mul, had, Matrix.det_one]
  have hd0 : d.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  set γ : M2 E N := Matrix.fromBlocks a 0 0 d with hγ
  have hU : γ ∈ UU E N := diag_mem_UU had
  obtain ⟨-, hZ', hIm, -⟩ := (unitary_act_halfSpace E Ψ N γ hU).2 Z hZ
  have hden : ∀ τ, (hDen Ψ γ Z τ).det = τ.1 d.det := fun τ => by
    simp only [hDen, hγ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.map_zero _ (map_zero τ.1), Matrix.zero_mul, zero_add]
    exact (τ.1.map_det d).symm
  set k : ℂ := ∏ τ : Ψ, τ.1 d.det ^ n with hk
  have hk0 : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by simpa using hd0)
  have hfac : hFac Ψ γ Z (0 : CM Ψ n N) 0 = k := by
    have h : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
    simp only [hFac, hden, h, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, hk]
  refine ⟨_, hZ', ?_, ?_⟩
  · have h1 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M φ hM hφ Z hZ).1 γ hU
    have h2 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (fun Λ x => φ Λ (x * a)) hM hψ _ hZ').2.2.2.1 k
    apply mul_left_cancel₀ hk0
    rw [← h2, ← hfac, ← h1, hfac]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have : weil Ψ γ (φ Λ) = (k • fun Λ x => φ Λ (x * a) : Fam E n N) Λ := by
      funext x
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn (φ Λ) (hφ Λ hΛ)).1 γ hU rfl x]
      simp [hγ, chiH, hk]
    simp only [this]
  · rw [← hIm, abs_norm_eq hΨ, mul_left_comm, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one, mul_one]
    intro τ _
    rw [hden, ← mul_pow, ← Complex.norm_conj (τ.1 a.det), ← Base.map_cc, ← norm_mul, ← map_mul,
      hdet]
    simp

omit [NumberField E] [IsCMField E] in

theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1.le

end GlobalTheory.SW.TwistBound

namespace GlobalTheory.SW

open TwistBound in

theorem twist_swd_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ hφ
  obtain ⟨B, hB0, hB⟩ := bounded_of_adm hφ
  obtain ⟨c, C₁, -, h1⟩ := GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level E (N + 1)
  obtain ⟨C₂, h2⟩ := GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded E Ψ hΨ n N hn hN hSW M (R * c)
  refine ⟨max C₁ 0 ^ ((n : ℝ) / 2) * (C₂ * B), fun 𝔛 hfg hag Z hZ => ?_⟩
  obtain ⟨a, ha, hidx, hadm⟩ := h1 n M R φ 𝔛 hφ hfg hag
  obtain ⟨-, -, -, hpos, ⟨R', hR'⟩, -⟩ := twist_admissible E n (N + 1) M R φ 𝔛 hφ hfg hag
  obtain ⟨Z', hZ', e1, e2⟩ := exists_moved hΨ hn hN hφ.pos.1 (fun Λ hΛ => isSB_of_adm hR' hΛ) ha
    (fun Λ hΛ => isSB_of_adm hadm hΛ) hZ
  have h3 := h2 _ hadm B (fun Λ hΛ x => by
    unfold twist
    split_ifs
    · exact hB Λ hΛ _
    · simpa using hB0) Z' hZ'
  have hD := detIm_nonneg hZ
  replace h3 : ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z' ^ ((n : ℝ) / 2) ≤ C₂ * B := by
    rw [← e1]; exact h3
  rw [e2, Real.mul_rpow (abs_nonneg _) hD] at h3
  have h4 : gidx 𝔛 ^ ((n : ℝ) / 2) ≤
      max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (le_max_right _ _) (abs_nonneg _)]
    exact Real.rpow_le_rpow hpos.le
      (hidx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
  have h5 : 0 ≤ max C₁ 0 ^ ((n : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  calc _ ≤ (max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2)) *
        ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) := by gcongr
    _ = max C₁ 0 ^ ((n : ℝ) / 2) * (‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ *
        (|((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) * detIm Z ^ ((n : ℝ) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 h5

end GlobalTheory.SW
end

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_siegelWeil_difference_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  atlas_forward_decl GlobalTheory.SW.twist_swd_bounded
end
