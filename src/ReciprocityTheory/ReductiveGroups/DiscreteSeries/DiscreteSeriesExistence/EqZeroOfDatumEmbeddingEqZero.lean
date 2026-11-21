import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem pdA_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at hg hh ⊢
  have e : (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hg, hh]

theorem pdA_inUJ_of_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  unfold inUJ
  have h1 : star k * k = 1 := Unitary.star_mul_self_of_mem hk.1
  rw [Matrix.star_eq_conjTranspose] at h1
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

def pdA_kg {ε : Fin n → Bool} (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) : S7.KG ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, pdA_inUJ_of_Kset hk⟩, hk⟩

theorem pdA_toMK_kg {ε : Fin n → Bool} (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    S7.toMK (pdA_kg k hk) = k := rfl

theorem pdA_toMK_one (ε : Fin n → Bool) : S7.toMK (1 : S7.KG ε) = 1 := rfl

private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTranspose_eq_self' (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

private theorem inUJ_exp_of_inG' {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) :
    inUJ ε (NormedSpace.exp A) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have h0 : Aᴴ * Jm ε = -(Jm ε * A) := by
    unfold inG at hA
    exact eq_neg_of_add_eq_zero_left hA
  have hAH : Aᴴ = Jm ε * (-A) * (Jm ε)⁻¹ := by
    rw [hinv]
    calc Aᴴ = Aᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Jm ε * (-A) * Jm ε := by rw [h0, Matrix.mul_neg, Matrix.neg_mul]
  have h1 : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  unfold inUJ
  rw [← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hU, hinv]
  simp only [Matrix.mul_assoc, hJJ']
  rw [h1, Matrix.mul_one]

theorem pdA_rdV_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (he : ∀ h, inUJ ε h → f h = f' h) {X g : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f' g := by
  have hX' : ∀ t : ℝ, inG ε ((t : ℂ) • X) := fun t => by
    unfold inG at hX ⊢
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [← smul_add, hX, smul_zero]
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X)) :=
    funext fun t => he _ (pdA_inUJ_mul hg (inUJ_exp_of_inG' (hX' t)))
  simp only [Formalism.REAL.RdV]
  rw [e]

private theorem inG_cpart1_and_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Formalism.REAL.cpart1 ε Z) ∧ inG ε (Formalism.REAL.cpart2 ε Z) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJH := Jm_conjTranspose_eq_self' ε
  have hJr : Formalism.REAL.Jm ε = Jm ε := rfl
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp [Complex.star_def]
  have hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp [Complex.star_def]
  unfold inG Formalism.REAL.cpart1 Formalism.REAL.cpart2
  simp only [hJr, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.smul_mul, Matrix.mul_smul,
    sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hJJ, hJJ', mul_one]
  rw [hs1, hs2]
  constructor <;> module

theorem pdA_eabV_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (he : ∀ h, inUJ ε h → f h = f' h) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Formalism.REAL.EabV ε a b f g = Formalism.REAL.EabV ε a b f' g := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV]
  rw [pdA_rdV_congr he h1 hg, pdA_rdV_congr he h2 hg]

theorem pdA_smooth_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ) (hf : Formalism.REAL.SmoothOnGV ε f) (hf' : Formalism.REAL.SmoothOnGV ε f') :
    Formalism.REAL.SmoothOnGV ε (fun x => f x + c • f' x) := by
  unfold Formalism.REAL.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · intro g hg hgJ
    show f g + c • f' g = F g + c • F' g
    rw [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

theorem pdA_smooth_eabV {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f) (a b : Fin n) :
    Formalism.REAL.SmoothOnGV ε (Formalism.REAL.EabV ε a b f) := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  exact pdA_smooth_add_smul Complex.I (Formalism.REAL.rdSmoothV n ε E f _ hf h1)
    (Formalism.REAL.rdSmoothV n ε E f _ hf h2)

theorem pdA_eabV_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    (φ : E →L[ℂ] ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    φ (Formalism.REAL.EabV ε a b f g) = Formalism.REAL.Eab ε a b (fun x => φ (f x)) g := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  unfold Formalism.REAL.SmoothOnGV at hf
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have key : ∀ X, inG ε X → φ (Formalism.REAL.RdV X f g) = Formalism.REAL.Rd X (fun x => φ (f x)) g := by
    intro X hX
    have hd := smBr_hasDerivAt_ext f F U g X hU hgU hg hF hfF hX
    have hd' : HasDerivAt (fun t : ℝ => φ (f (g * NormedSpace.exp ((t : ℂ) • X))))
        (φ (fderiv ℝ F g (g * X))) 0 :=
      (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    simp only [Formalism.REAL.RdV, Formalism.REAL.Rd]
    rw [hd.deriv, hd'.deriv]
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV, Formalism.REAL.Eab, Formalism.REAL.Ec, map_add, map_smul, smul_eq_mul]
  rw [key _ h1, key _ h2]

theorem pdA_casF_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    (φ : E →L[ℂ] ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Formalism.REAL.CasF ε (fun x => φ (f x)) g = φ (S7.casimirV ε f g) := by
  have hE : ∀ (F : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n),
      S7.EabV ε a b F = Formalism.REAL.EabV ε a b F := fun _ _ _ => rfl
  simp only [Formalism.REAL.CasF, S7.casimirV, map_sum, hE]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pdA_eabV_clm φ (pdA_smooth_eabV hf b a) a b hg]
  exact pdA_eabV_congr (f := Formalism.REAL.Eab ε b a fun x => φ (f x))
    (fun h hh => (pdA_eabV_clm φ hf b a hh).symm) a b hg


def pdA_coef {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v₀ v : V) : (V →L[ℂ] V) →L[ℂ] ℂ :=
  (innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ V v)

theorem pdA_smooth_clm {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {ε : Fin n → Bool} (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : Formalism.REAL.SmoothOnGV ε f) : Formalism.REAL.SmoothOnGV ε (fun x => φ (f x)) := by
  unfold Formalism.REAL.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hgU, ?_, fun g hg hgJ => by simp only [hfF g hg hgJ]⟩
  exact (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF

theorem pdA_single_comm {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs <;> simp_all

theorem pdA_inK_cpart {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z * Jm ε = Jm ε * Z) :
    inK ε (Formalism.REAL.cpart1 ε Z) ∧ inK ε (Formalism.REAL.cpart2 ε Z) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hZH : Zᴴ * Jm ε = Jm ε * Zᴴ := by
    have e := congrArg Matrix.conjTranspose hZ
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at e
    exact e.symm
  have hJr : Formalism.REAL.Jm ε = Jm ε := rfl
  refine ⟨⟨(inG_cpart1_and_inG_cpart2 ε Z).1, ?_⟩, ⟨(inG_cpart1_and_inG_cpart2 ε Z).2, ?_⟩⟩
  · simp only [Formalism.REAL.cpart1, hJr, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, Matrix.mul_assoc,
      hJJ, hJJ', mul_one, hZ, hZH]
  · simp only [Formalism.REAL.cpart2, hJr, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.mul_assoc,
      hJJ, hJJ', mul_one, hZ, hZH]

theorem pdA_inK_smul {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at h1 ⊢
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

theorem pdA_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) : T.op 1 = 1 := by
  simp [S7.KType.op]

private theorem exp_smul_mem_Kset_of_inK {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  obtain ⟨hG, hC⟩ := pdA_inK_smul hX t
  set A := (t : ℂ) • X with hAdef
  have h0 : Aᴴ * Jm ε = -(Jm ε * A) := by
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  have hAH : Aᴴ = -A := by
    calc Aᴴ = Aᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -A := by rw [h0, ← hC, Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hconj : Jm ε * A * (Jm ε)⁻¹ = A := by
    rw [hinv, ← hC, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  unfold Kset
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hAH,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  · have e := Matrix.exp_conj (Jm ε) A hU
    rw [hconj, hinv] at e
    calc NormedSpace.exp A * Jm ε = Jm ε * NormedSpace.exp A * Jm ε * Jm ε := by rw [← e]
      _ = Jm ε * NormedSpace.exp A := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]

theorem pdA_rdV_compact {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hΨ : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    (v₀ v : T.V) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hg : inUJ ε g) :
    Formalism.REAL.RdV X (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ X v)) := by
  have hexp := exp_smul_mem_Kset_of_inK hX
  let γ : ℝ → S7.KG ε := fun t => pdA_kg (NormedSpace.exp ((t : ℂ) • X)) (hexp t)
  have hγ : ∀ t, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := fun t => pdA_toMK_kg _ _
  have hd := T.hasDeriv X hX γ hγ
  let L : (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    ((innerSL ℂ v₀).comp (Ψ g)).comp (ContinuousLinearMap.apply ℂ T.V v)
  have hf : (fun t : ℝ => inner ℂ v₀ (Ψ (g * NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => L (T.op (γ t)) := by
    funext t
    have e := hΨ 1 (γ t) g hg
    rw [pdA_toMK_one, hγ t, Matrix.one_mul, pdA_op_one, one_mul] at e
    rw [e]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => L (T.op (γ t))) (L (T.dτ X)) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  simp only [Formalism.REAL.RdV]
  rw [hf, hd2.deriv]
  rfl

theorem pdA_eab_compact {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hΨ : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ (Matrix.single a b 1) v)) := by
  obtain ⟨h1, h2⟩ := pdA_inK_cpart (pdA_single_comm (ε := ε) hab)
  have e1 : Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g =
      inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) v)) :=
    pdA_rdV_compact T hΨ v₀ v h1 hg
  have e2 : Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g =
      inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) v)) :=
    pdA_rdV_compact T hΨ v₀ v h2 hg
  have hZ : Matrix.single a b (1 : ℂ) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) +
      Complex.I • Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.REAL.cpart1 Formalism.REAL.cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
    module
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec]
  rw [e1, e2]
  conv_rhs => rw [hZ]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]

open scoped Classical in

theorem toL2_congr_of_forall_inUJ_eq {ε : Fin n → Bool} {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F g = G g) : toL2 ε F = toL2 ε G := by
  have hfg : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h (Formalism.MainNotions.S.umat g) g.2
  unfold toL2
  simp only [hfg]

theorem toL2_finset_sum_of_memLp {ε : Fin n → Bool} {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, MemLp (fun g : Formalism.REAL.UJ ε => F i (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, toL2 ε (F i) := by
  classical
  have key : ∀ (H : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (hH : MemLp (fun g : Formalism.REAL.UJ ε => H (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)),
      toL2 ε H = hH.toLp _ := fun H hH => by
    unfold toL2
    rw [dif_pos hH]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold toL2
    split_ifs with h
    · exact MemLp.toLp_zero h
    · rfl
  | @insert j s hj ih =>
    have hG : MemLp (fun g : Formalism.REAL.UJ ε => (fun x => ∑ i ∈ s, F i x) (Formalism.MainNotions.S.umat g)) 2
        (Formalism.REAL.muG ε) := memLp_finset_sum s (fun i _ => hF i)
    rw [Finset.sum_insert hj, ← ih]
    have e : (fun x => ∑ i ∈ insert j s, F i x) = fun x => F j x + ∑ i ∈ s, F i x := by
      funext x
      exact Finset.sum_insert hj
    rw [e, key (fun x => F j x + ∑ i ∈ s, F i x) ((hF j).add hG), key (F j) (hF j),
      key (fun x => ∑ i ∈ s, F i x) hG]
    exact MemLp.toLp_add (hF j) hG

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsPsiFor (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
    Ψ 1 = 1 ∧ S7.SmoothOnGV ε Ψ ∧
    (∀ g, inUJ ε g → S7.casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
    ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure → MemLp (fun g : S7.UJ ε => Ψ (S7.toM g)) 2 μ

theorem exists_isPsiFor (hS7 : S7.PsiExistsStatement n) {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    (T : S7.KType ε (lowK ε lam)) (hlam : S7.IsHCParam lam) (hh : GapAtLeast ε lam h) (hq : 1 ≤ S7.q0 ε)
    (h8 : 8 * (n : ℝ) * S7.q0 ε < h) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), IsPsiFor ε lam T Ψ ∧
      ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := by
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6⟩ := hS7 ε lam h T hlam hh hq
  exact ⟨Ψ, ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 h8⟩, h5⟩

section Datum

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}

def jfun (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ v : T.V) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => inner ℂ v₀ (Ψ g v)

def uniformisationL2 (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ v : T.V) : L2 ε :=
  toL2 ε (jfun Ψ v₀ v)

def datumV (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    Submodule ℂ (smD ε (rreg ε)) :=
  (Submodule.span ℂ (Set.range (uniformisationL2 ε Ψ v₀))).comap (smD ε (rreg ε)).subtype

variable {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem jfun_CasF (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.CasF ε (jfun Ψ v₀ v) g = ((casVal lam : ℝ) : ℂ) * jfun Ψ v₀ v g := by
  intro g hg
  have e := pdA_casF_clm (pdA_coef v₀ v) (f := Ψ) hP.2.2.1 (g := g) hg
  rw [show jfun Ψ v₀ v = fun x => pdA_coef v₀ v (Ψ x) from rfl, e, hP.2.2.2.1 g hg, map_smul, smul_eq_mul]

def dt_jfunLin (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) :
    T.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun := jfun Ψ v₀
  map_add' v w := funext fun x => by simp [jfun]
  map_smul' c v := funext fun x => by simp [jfun]

theorem dt_memLp (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have hH : (Formalism.REAL.muG ε).IsHaarMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  have h := hP.2.2.2.2 (Formalism.REAL.muG ε) hH
  exact ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v)).comp_memLp' h

theorem datumFunction_isSmoothL2 (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) : IsSmoothL2 ε (jfun Ψ v₀ v) := by
  refine isSmoothL2_of_casimir_eigen ε (LinearMap.range (dt_jfunLin Ψ v₀)) ((casVal lam : ℝ) : ℂ) inferInstance
    ?_ ?_ ?_ ?_ (jfun Ψ v₀ v) (LinearMap.mem_range.2 ⟨v, rfl⟩)
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact pdA_smooth_clm (pdA_coef v₀ u) (f := Ψ) hP.2.2.1
  · intro w hw i j hij
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact ⟨jfun Ψ v₀ (T.dτ (Matrix.single i j 1) u), LinearMap.mem_range.2 ⟨_, rfl⟩,
      fun g hg => pdA_eab_compact T hP.1 v₀ u hij hg⟩
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact jfun_CasF hP v₀ u
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
    exact dt_memLp hP v₀ u

theorem datumEmbedding_mem_smooth (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) : uniformisationL2 ε Ψ v₀ v ∈ smD ε (rreg ε) := by
  exact toL2_mem_smD_of_isSmoothL2 (datumFunction_isSmoothL2 hP v₀ v)

theorem datumEmbedding_add (hP : IsPsiFor ε lam T Ψ) (v₀ v v' : T.V) :
    uniformisationL2 ε Ψ v₀ (v + v') = uniformisationL2 ε Ψ v₀ v + uniformisationL2 ε Ψ v₀ v' := by
  have h1 := dt_memLp hP v₀ v
  have h2 := dt_memLp hP v₀ v'
  have h3 := dt_memLp hP v₀ (v + v')
  simp only [uniformisationL2, toL2, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp [jfun, inner_add_right])

theorem datumEmbedding_smul (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) (c : ℂ) (v : T.V) :
    uniformisationL2 ε Ψ v₀ (c • v) = c • uniformisationL2 ε Ψ v₀ v := by
  have h1 := dt_memLp hP v₀ v
  have h3 := dt_memLp hP v₀ (c • v)
  simp only [uniformisationL2, toL2, dif_pos h1, dif_pos h3]
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp [jfun, inner_smul_right])

def datumEmbeddingToL2 (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] L2 ε where
  toFun := uniformisationL2 ε Ψ v₀
  map_add' := datumEmbedding_add hP v₀
  map_smul' := datumEmbedding_smul hP v₀

private theorem toL2_congr_of_eq_on_umat (F G : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g : Formalism.REAL.UJ ε, F (Formalism.MainNotions.S.umat g) = G (Formalism.MainNotions.S.umat g)) : toL2 ε F = toL2 ε G := by
  have hfg : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) := funext h
  unfold toL2
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hfg ▸ hF
    rw [dif_pos hF, dif_pos hG]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall h)
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hfg ▸ hF
    rw [dif_neg hF, dif_neg hG]

theorem rightRegular_datumEmbedding (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) (k : S7.KG ε) :
    rreg ε (S7.toMK k) (uniformisationL2 ε Ψ v₀ v) = uniformisationL2 ε Ψ v₀ (T.op k v) := by
  have hk : S7.toMK k ∈ UJset ε := by
    simp [S7.toMK, UJset]
    exact (k : S7.UJ ε).2
  rw [uniformisationL2, uniformisationL2, rightRegular_toL2 ε _ hk]
  apply toL2_congr_of_eq_on_umat
  intro x
  have h1 := hP.1 1 k (Formalism.MainNotions.S.umat x) x.2
  rw [show S7.toMK (1 : S7.KG ε) = 1 by simp [S7.toMK], one_mul] at h1
  simp only [jfun]
  rw [h1]
  clear h1 hk hP
  first
  | rw [T.op_one]; simp
  | rw [T.map_one]; simp
  | rw [map_one]; simp
  | simp [S7.KType.op]

theorem rightDerivative_datum_embedding (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    ((smE ε (rreg ε) a b ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩ : smD ε (rreg ε)) : L2 ε) =
      uniformisationL2 ε Ψ v₀ (T.dτ (Matrix.single a b 1) v) := by
  exact (rightDerivative_toL2 (datumFunction_isSmoothL2 hP v₀ v) a b).trans
    (toL2_congr_of_forall_inUJ_eq fun g hg => pdA_eab_compact T hP.1 v₀ v hab hg)

theorem mem_datumV_iff (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) (x : smD ε (rreg ε)) :
    x ∈ datumV ε Ψ v₀ ↔ ∃ v : T.V, (x : L2 ε) = uniformisationL2 ε Ψ v₀ v := by
  have hr : Set.range (uniformisationL2 ε Ψ v₀) =
      ((LinearMap.range (datumEmbeddingToL2 hP v₀) : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    ext x
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    rfl
  simp only [datumV, Submodule.mem_comap, Submodule.coe_subtype]
  rw [hr, Submodule.span_eq, LinearMap.mem_range]
  exact exists_congr fun w => eq_comm

theorem datumV_casimir (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    ∀ v ∈ datumV ε Ψ v₀, casimir (smE ε (rreg ε)) v = ((casVal lam : ℝ) : ℂ) • v := by
  intro x hx
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hF := datumFunction_isSmoothL2 hP v₀ v
  have hx' : x = ⟨toL2 ε (jfun Ψ v₀ v), toL2_mem_smD_of_isSmoothL2 hF⟩ := Subtype.ext hv
  have key : ∀ a b, ((smE ε (rreg ε) a b (smE ε (rreg ε) b a x) : smD ε (rreg ε)) : L2 ε) =
      toL2 ε (Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v))) := by
    intro a b
    have h1 : smE ε (rreg ε) b a x =
        ⟨toL2 ε (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)), toL2_mem_smD_of_isSmoothL2 (hF.Eab b a)⟩ :=
      Subtype.ext (by rw [hx']; exact rightDerivative_toL2 hF b a)
    rw [h1]
    exact rightDerivative_toL2 (hF.Eab b a) a b
  have hG : ∀ a b, MemLp (fun g : Formalism.REAL.UJ ε =>
      Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun a b => ((hF.Eab b a).Eab a b).2 []
  apply Subtype.ext
  rw [Submodule.coe_smul, hv]
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, key]
  calc ∑ a, ∑ b, toL2 ε (Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)))
      = ∑ a, toL2 ε (fun x => ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x) :=
        Finset.sum_congr rfl fun a _ => (toL2_finset_sum_of_memLp _ _ fun b => hG a b).symm
    _ = toL2 ε (fun x => ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x) :=
        (toL2_finset_sum_of_memLp _ (fun a x => ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (jfun Ψ v₀ v)) x)
          fun a => memLp_finsetSum _ fun b _ => hG a b).symm
    _ = toL2 ε (((casVal lam : ℝ) : ℂ) • jfun Ψ v₀ v) := toL2_congr_of_forall_inUJ_eq fun g hg => by
        rw [Pi.smul_apply, smul_eq_mul, ← jfun_CasF hP v₀ v g hg]
        rfl
    _ = ((casVal lam : ℝ) : ℂ) • uniformisationL2 ε Ψ v₀ v := toL2_smul_smooth ε _ _

theorem datumV_kStable (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    ∀ k ∈ Kset ε, ∀ v ∈ datumV ε Ψ v₀, ∃ w ∈ datumV ε Ψ v₀, (w : L2 ε) = rreg ε k v := by
  intro k hk x hx
  obtain ⟨u, hu⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hK : ∃ k' : S7.KG ε, S7.toMK k' = k := by
    clear hu hx hP
    refine ⟨⟨⟨⟨k, star k, ?_, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · exact Matrix.mem_unitaryGroup_iff.1 hk.1
    · exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    · show kᴴ * Jm ε * k = Jm ε
      rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Matrix.mem_unitaryGroup_iff'.1 hk.1, Matrix.one_mul]
    · first
      | exact hk
      | exact ⟨hk.1, hk.2⟩
      | exact hk.2
      | exact hk.2.symm
      | (simp only [S7.KG, Kset] at hk ⊢; done)
  obtain ⟨k', rfl⟩ := hK
  refine ⟨⟨uniformisationL2 ε Ψ v₀ (T.op k' u), datumEmbedding_mem_smooth hP v₀ _⟩, (mem_datumV_iff hP v₀ _).2 ⟨_, rfl⟩, ?_⟩
  rw [hu, rightRegular_datumEmbedding hP v₀ u k']

theorem datumEmbedding_self_ne_zero (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) : uniformisationL2 ε Ψ v₀ v₀ ≠ 0 := by
  intro h0
  have hm := dt_memLp hP v₀ v₀
  have hc : Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat g)) := by
    rw [continuous_iff_continuousAt]
    intro g
    obtain ⟨U, F, hU, hgU, hF, hEq⟩ := hP.2.2.1 (Formalism.MainNotions.S.umat g) g.2
    have hFc : ContinuousAt F (Formalism.MainNotions.S.umat g) := by
      first
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
      | (letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
         letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedSpace
         exact hF.continuousOn.continuousAt (hU.mem_nhds hgU))
    have hev : (fun y : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat y)) =ᶠ[nhds g]
        fun y => inner ℂ v₀ (F (Formalism.MainNotions.S.umat y) v₀) := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with y hy
      simp only [jfun, hEq _ hy y.2]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ T.V v₀)).continuous.continuousAt.comp
      (hFc.comp hc.continuousAt)
  have hae : (fun g : Formalism.REAL.UJ ε => jfun Ψ v₀ v₀ (Formalism.MainNotions.S.umat g)) =ᵐ[Formalism.REAL.muG ε] 0 := by
    have h1 : uniformisationL2 ε Ψ v₀ v₀ = hm.toLp _ := by simp only [uniformisationL2, toL2, dif_pos hm]
    rw [h1] at h0
    have h2 := hm.coeFn_toLp
    rw [h0] at h2
    exact h2.symm.trans (Lp.coeFn_zero ℂ 2 (Formalism.REAL.muG ε))
  haveI : (Formalism.REAL.muG ε).IsOpenPosMeasure := by
    unfold Formalism.REAL.muG
    infer_instance
  have hall := (Continuous.ae_eq_iff_eq (Formalism.REAL.muG ε) hcont continuous_zero).1 hae
  have h1 := congrFun hall 1
  simp [jfun, hP.2.1] at h1
  have hu1 : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  rw [hu1, hP.2.1] at h1
  simp at h1
  exact hv₀ h1

theorem eq_zero_of_datumEmbedding_eq_zero (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) {v : T.V}
    (h : uniformisationL2 ε Ψ v₀ v = 0) : v = 0 := by
  have hst : ∀ k : S7.KG ε, ∀ u ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀),
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) u ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := by
    intro k u hu
    have hu' : uniformisationL2 ε Ψ v₀ u = 0 := LinearMap.mem_ker.1 hu
    apply LinearMap.mem_ker.2
    show uniformisationL2 ε Ψ v₀ (T.op k u) = 0
    rw [← rightRegular_datumEmbedding hP v₀ u k, hu', map_zero]
  rcases T.irred _ hst with hb | ht
  · have hm : v ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := LinearMap.mem_ker.2 h
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · have hm : v₀ ∈ LinearMap.ker (datumEmbeddingToL2 hP v₀) := by rw [ht]; trivial
    exact absurd (LinearMap.mem_ker.1 hm) (datumEmbedding_self_ne_zero hP hv₀)

theorem datumV_ne_bot (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) : datumV ε Ψ v₀ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨uniformisationL2 ε Ψ v₀ v₀, datumEmbedding_mem_smooth hP v₀ v₀⟩, (mem_datumV_iff hP v₀ _).2 ⟨v₀, rfl⟩, ?_⟩
  intro h0
  exact datumEmbedding_self_ne_zero hP hv₀ (congrArg Subtype.val h0)

theorem datumV_weight_le (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) {μ : Fin n → ℝ}
    {x : smD ε (rreg ε)} (hx : x ∈ datumV ε Ψ v₀) (hx0 : x ≠ 0)
    (hμ : ∀ a, smE ε (rreg ε) a a x = ((μ a : ℝ) : ℂ) • x) :
    Formalism.MainNotions.S.CDom ε μ (lowK ε lam) := by
  obtain ⟨v, hv⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hxe : x = ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩ := Subtype.ext hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hx0
    apply Subtype.ext
    rw [hv]
    exact (datumEmbeddingToL2 hP v₀).map_zero
  have hμ' : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
    intro a
    have e1 := rightDerivative_datum_embedding hP v₀ v (a := a) (b := a) rfl
    have e2 := congrArg Subtype.val (hμ a)
    rw [hxe] at e2
    rw [e1, Submodule.coe_smul] at e2
    have e3 : datumEmbeddingToL2 hP v₀ (T.dτ (Matrix.single a a 1) v - ((μ a : ℝ) : ℂ) • v) = 0 := by
      rw [map_sub, map_smul]
      exact sub_eq_zero.2 e2
    exact sub_eq_zero.1 (eq_zero_of_datumEmbedding_eq_zero hP hv₀ e3)
  obtain ⟨c, hc1, hc2⟩ := HW.KType.weight_le T hv0 hμ'
  exact ⟨c, hc1, hc2⟩

end Datum

end ReciprocityTheory.ChartRestriction.DS
end
end
