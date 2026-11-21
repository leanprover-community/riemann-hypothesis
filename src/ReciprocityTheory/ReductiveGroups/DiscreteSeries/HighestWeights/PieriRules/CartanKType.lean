import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CountNotTwoOfFinrankLeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7




theorem pieriSt_kRel_stdM {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.KRel ε (stdM n) := by
  intro a b c d _ _
  simp only [stdM]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pieriSt_stdM_diag {n : ℕ} (a : Fin n) :
    stdM n a a = Matrix.diagonal fun i => ((stdWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai; simp [stdM, stdWt]
    · simp [stdM, stdWt, hai, Pi.single_apply]
  · simp [stdM, Matrix.single_apply, hij]
    intro h1 h2; exact hij (h1.symm.trans h2)




end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def stdRho (ε : Fin n → Bool) : KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ) where
  toFun k := ⟨toMK k, k.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem stdRho_apply (ε : Fin n → Bool) (k : KG ε) :
    ((stdRho ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) = toMK k := rfl

theorem stdRho_cont (ε : Fin n → Bool) :
    Continuous (fun k : KG ε => ((stdRho ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ)) :=
  (continuous_toM ε).comp continuous_subtype_val

theorem std_exp_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ)
  have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    _ h
  have h3 := hasDerivAt_real_of_complex' (z := 0) h2
  have h4 : (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by
    simp
  exact h3.congr_deriv h4

theorem stdRho_hasDeriv (ε : Fin n → Bool) :
    ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((stdRho ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j)
        ((LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) X i j) 0 := by
  intro X _ γ hγ i j
  have e : (fun t : ℝ => ((stdRho ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j := by
    funext t
    rw [stdRho_apply, hγ t]
  rw [e]
  exact std_exp_entry_hasDerivAt X i j

theorem stdWt_injective (n : ℕ) : Function.Injective (stdWt n) := by
  intro i j h
  have h1 := congrFun h i
  simp only [stdWt, Pi.single_eq_same] at h1
  by_contra hij
  rw [Pi.single_eq_of_ne hij] at h1
  exact one_ne_zero h1

theorem stdWt_card (Λ : Fin n → ℝ) (s : Fin n) :
    Nat.card {i : Fin n // Λ + stdWt n s = Λ + stdWt n i} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨s, rfl⟩, fun x => Subtype.ext ?_⟩
  exact (stdWt_injective n (add_left_cancel x.2)).symm

theorem pieriStd_of_props (hcount : PieriCountStatement) (htens : TensHWStatement)
    (hsum : WeylSumStdStatement) (hdom : KTypeIntDomStatement) : PieriStdStatement := by
  intro n ε Λ T
  obtain ⟨hint, hkd⟩ := hdom n ε Λ T
  obtain ⟨hs, hvan⟩ := hsum n ε Λ hint hkd
  have hs' : ∑ i, weylK ε (Λ + stdWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ := by
    rw [Fintype.card_fin]; exact hs
  have hc := hcount n ε Λ T (Fin n) (stdRho ε) LinearMap.id (stdWt n) (stdRho_cont ε)
    (stdRho_hasDeriv ε) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag (stdWt_injective n) hs' hvan
  have ht := htens T.V n ε (kunits T) Λ T.w (Fin n) (stdM n) (stdWt n) (KType.kRel T) (KType.kUnit T)
    (KType.kHighest_w T) (KType.kSpan_eq_top T) (pieriSt_kRel_stdM ε) pieriSt_stdM_diag
  refine ⟨hc.2, fun s => ?_, hc.1⟩
  have h := (ht.2 (Λ + stdWt n s)).2
  rw [stdWt_card Λ s] at h
  exact h

theorem pieriStd_of (hc : CompRedStatement) (hr : KRepRelStatement) : PieriStdStatement :=
  pieriStd_of_props (pieriCount_of hc hr) tensHW weylSumStd kTypeIntDom

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

abbrev conjMat : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ := (starRingEnd ℂ).mapMatrix

theorem conjMat_star (g : Matrix (Fin n) (Fin n) ℂ) : star (conjMat g) = conjMat (star g) := by
  ext i j
  simp [Matrix.star_apply, RingHom.mapMatrix_apply]

theorem conjMat_mem_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    conjMat g ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  rw [Unitary.mem_iff] at hg ⊢
  rw [conjMat_star, ← map_mul, ← map_mul, hg.1, hg.2, map_one]
  exact ⟨rfl, rfl⟩

def rhoDual (ε : Fin n → Bool) : KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ) where
  toFun k := ⟨conjMat (toMK k), conjMat_mem_unitary k.2.1⟩
  map_one' := by
    apply Subtype.ext
    show conjMat (toMK (1 : KG ε)) = 1
    rw [show toMK (1 : KG ε) = 1 from rfl, map_one]
  map_mul' k l := by
    apply Subtype.ext
    show conjMat (toMK (k * l)) = conjMat (toMK k) * conjMat (toMK l)
    rw [show toMK (k * l) = toMK k * toMK l from rfl, map_mul]

theorem rhoDual_apply (ε : Fin n → Bool) (k : KG ε) (i j : Fin n) :
    ((rhoDual ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) i j =
      star (toMK k i j) := rfl

def dualD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := -Xᵀ
  map_add' X Y := by rw [Matrix.transpose_add, neg_add]
  map_smul' c X := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem dualD_apply (X : Matrix (Fin n) (Fin n) ℂ) : dualD X = -Xᵀ := rfl

theorem dualD_single (a b : Fin n) : dualD (Matrix.single a b (1 : ℂ)) = dualM n a b := by
  rw [dualD_apply, Matrix.transpose_single]
  rfl

theorem dualD_units : (fun a b : Fin n => dualD (Matrix.single a b (1 : ℂ))) = dualM n := by
  funext a b
  exact dualD_single a b

theorem continuous_rhoDual (ε : Fin n → Bool) :
    Continuous (fun k : KG ε => ((rhoDual ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ)) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (continuous_id.matrix_map continuous_star).comp hK

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h0 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h1 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) =
      fun t : ℝ => LinearMap.toContinuousLinearMap L (NormedSpace.exp (t • X)) := by
    funext t
    rw [Complex.coe_smul]
    rfl
  rw [e]
  exact h1

end Deriv

theorem hasDeriv_rhoDual (ε : Fin n → Bool) :
    ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((rhoDual ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j) (dualD X i j) 0 := by
  intro X hX γ hγ i j
  have hskew : Xᴴ = -X := ((inK_iff' ε X).1 hX).1
  have hval : star (X i j) = -X j i := by
    have := congrFun (congrFun hskew j) i
    simpa [Matrix.conjTranspose_apply] using this
  have h := (exp_entry_hasDerivAt X i j).star
  rw [dualD_apply, Matrix.neg_apply, Matrix.transpose_apply, ← hval]
  have e : (fun t : ℝ => ((rhoDual ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => star (NormedSpace.exp ((t : ℂ) • X) i j) := by
    funext t
    rw [rhoDual_apply, hγ t]
  rw [e]
  exact h

theorem kRel_dualM (ε : Fin n → Bool) : Formalism.REAL.KRel ε (dualM n) := by
  intro a b c d _ _
  simp only [dualM, neg_mul_neg]
  rcases eq_or_ne a d with rfl | hda <;> rcases eq_or_ne c b with rfl | hcb
  · simp only [Matrix.single_mul_single_same, mul_one, if_true]
    abel
  · simp [hcb.symm]
    exact Matrix.single_mul_single_of_ne (h := hcb) ..
  · simp [hda.symm]
    exact Matrix.single_mul_single_of_ne (h := hda) ..
  · simp only [hda.symm, hcb.symm, if_false, sub_zero]
    rw [Matrix.single_mul_single_of_ne (h := hda) .., Matrix.single_mul_single_of_ne (h := hcb) .., sub_zero]

theorem dualM_diag (a : Fin n) :
    dualM n a a = Matrix.diagonal fun i => ((dualWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai
      simp [dualM, dualWt]
    · simp [dualM, dualWt, hai, Pi.single_apply]
  · simp [dualM, Matrix.single_apply, hij]
    intro h1 h2
    exact hij (h1.symm.trans h2)

theorem dualWt_injective : Function.Injective (dualWt n) := by
  intro i j h
  have h' := congrFun h i
  by_contra hne
  simp [dualWt, Ne.symm hne] at h'

theorem pieriDual_of_st (hcount : PieriCountStatement) (hws : WeylSumDualStatement)
    (hkt : KTypeIntDomStatement) (hth : TensHWStatement) : PieriDualStatement := by
  intro n ε Λ T
  obtain ⟨hint, hdom⟩ := hkt n ε Λ T
  obtain ⟨hsum, hvan⟩ := hws n ε Λ hint hdom
  have hdiag : ∀ a, dualD (Matrix.single a a (1 : ℂ)) =
      Matrix.diagonal fun i => ((dualWt n i a : ℝ) : ℂ) := fun a => by
    rw [dualD_single, dualM_diag]
  have hrel : Formalism.REAL.KRel ε (fun a b => dualD (Matrix.single a b (1 : ℂ))) := by
    rw [dualD_units]
    exact kRel_dualM ε
  have hsum' : ∑ i, weylK ε (Λ + dualWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ := by
    rw [Fintype.card_fin]
    exact hsum
  obtain ⟨hex, hall⟩ := hcount n ε Λ T (Fin n) (rhoDual ε) dualD (dualWt n) (continuous_rhoDual ε)
    (hasDeriv_rhoDual ε) hrel hdiag dualWt_injective hsum' hvan
  rw [dualD_units] at hex hall
  have hfin := (hth T.V n ε (kunits T) Λ T.w (Fin n) (dualM n) (dualWt n) (KType.kRel T)
    (KType.kUnit T) (KType.kHighest_w T) (KType.kSpan_eq_top T) (kRel_dualM ε) dualM_diag).2
  refine ⟨hall, fun s => ?_, hex⟩
  refine (hfin (Λ + dualWt n s)).2.trans (le_of_eq ?_)
  have hiff : ∀ i, (Λ + dualWt n s = Λ + dualWt n i) ↔ i = s := fun i =>
    ⟨fun h => (dualWt_injective (add_left_cancel h)).symm, fun h => h ▸ rfl⟩
  simp_rw [hiff]
  simp

theorem pieriDual_of (hc : CompRedStatement) (hr : KRepRelStatement) : PieriDualStatement :=
  pieriDual_of_st (pieriCount_of hc hr) weylSumDual kTypeIntDom tensHW

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix Finset
open scoped Kronecker

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma prho_submatrix_mul {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (A B : Matrix ι ι ℂ) (hA : ∀ i k, P i → ¬ P k → A i k = 0) :
    ((A * B).submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) =
      (A.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) *
        (B.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) := by
  ext p r
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := P) (fun k _ hk => by_contra fun h => hk (by rw [hA _ _ p.2 h, zero_mul]))]
  exact Finset.sum_subtype _ (fun k => by simp) _

lemma prho_sub_kron {ι κ : Type*} (A B : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, sub_mul]

lemma prho_kron_sub {ι κ : Type*} (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, mul_sub]

def adFull (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  g ⊗ₖ g.map (starRingEnd ℂ)

def adDFull (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  X ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Xᵀ

lemma adFull_mul (g h : Matrix (Fin n) (Fin n) ℂ) : adFull (g * h) = adFull g * adFull h := by
  unfold adFull
  rw [Matrix.map_mul, mul_kronecker_mul]

lemma adFull_one : adFull (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold adFull
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _), one_kronecker_one]

lemma adFull_star (g : Matrix (Fin n) (Fin n) ℂ) : star (adFull g) = adFull (star g) := by
  ext p q
  simp only [adFull, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul',
    RCLike.star_def, RCLike.conj_conj]

lemma adDFull_bracket (X Y : Matrix (Fin n) (Fin n) ℂ) :
    adDFull X * adDFull Y - adDFull Y * adDFull X = adDFull (X * Y - Y * X) := by
  simp only [adDFull, sub_mul, mul_sub, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.transpose_sub, Matrix.transpose_mul, prho_sub_kron, prho_kron_sub]
  abel

variable {ε : Fin n → Bool} {β : Bool}

lemma adFull_zero_out {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adFull g p k = 0 := by
  simp only [adFull, Matrix.kroneckerMap_apply, Matrix.map_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    rw [uq_offdiag_zero hg h2, map_zero, mul_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    rw [uq_offdiag_zero hg h2, zero_mul]

lemma adDFull_zero_out {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adDFull X p k = 0 := by
  simp only [adDFull, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    have h3 : p.2 ≠ k.2 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX (Ne.symm h2), mul_zero, mul_zero, sub_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    have h3 : p.1 ≠ k.1 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX h2, zero_mul, zero_mul, sub_zero]

variable (ε β)

def pRhoM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (pIdx ε β) (pIdx ε β) ℂ :=
  (adFull g).submatrix Subtype.val Subtype.val

lemma pRhoM_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (h : Matrix (Fin n) (Fin n) ℂ) :
    pRhoM ε β (g * h) = pRhoM ε β g * pRhoM ε β h := by
  unfold pRhoM
  rw [adFull_mul]
  exact prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
    (fun i k hi hk => adFull_zero_out hg i k hi hk)

lemma pRhoM_one : pRhoM ε β (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold pRhoM
  rw [adFull_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

lemma pRhoM_star (g : Matrix (Fin n) (Fin n) ℂ) : star (pRhoM ε β g) = pRhoM ε β (star g) := by
  unfold pRhoM
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, ← Matrix.star_eq_conjTranspose,
    adFull_star]

lemma pRhoM_mem (k : KG ε) : pRhoM ε β (toMK k) ∈ unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) := by
  have hk : toMK k ∈ Kset ε := k.2
  have hs : star (toMK k) ∈ Kset ε := Kset_star ε hk
  rw [Unitary.mem_iff, pRhoM_star, ← pRhoM_mul ε β hs.2, ← pRhoM_mul ε β hk.2,
    Unitary.star_mul_self_of_mem hk.1, Unitary.mul_star_self_of_mem hk.1, pRhoM_one]
  exact ⟨rfl, rfl⟩

def pRho : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) where
  toFun k := ⟨pRhoM ε β (toMK k), pRhoM_mem ε β k⟩
  map_one' := Subtype.ext (pRhoM_one ε β)
  map_mul' k l := Subtype.ext (pRhoM_mul ε β (k.2 : toMK k ∈ Kset ε).2 (toMK l))

lemma pRho_apply (k : KG ε) (p q : pIdx ε β) :
    ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) p q =
      toMK k p.1.1 q.1.1 * star (toMK k p.1.2 q.1.2) := rfl

def pDRho : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ where
  toFun X := (adDFull X).submatrix Subtype.val Subtype.val
  map_add' X Y := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    ring
  map_smul' c X := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma pDRho_apply (X : Matrix (Fin n) (Fin n) ℂ) (p q : pIdx ε β) :
    pDRho ε β X p q = X p.1.1 q.1.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.1.2 q.1.2 -
      (1 : Matrix (Fin n) (Fin n) ℂ) p.1.1 q.1.1 * X q.1.2 p.1.2 := rfl

theorem pDRho_single (a b : Fin n) : pDRho ε β (Matrix.single a b 1) = pAdM ε β a b := by
  ext p q
  rw [pDRho_apply]
  simp only [pAdM, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : p.1.1 = a <;> by_cases h2 : q.1.1 = b <;> by_cases h3 : p.1.2 = q.1.2 <;>
    by_cases h4 : q.1.2 = a <;> by_cases h5 : p.1.2 = b <;> by_cases h6 : p.1.1 = q.1.1 <;>
    simp_all [eq_comm]

theorem pDRho_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    (hY : Y * Jm ε = Jm ε * Y) :
    pDRho ε β X * pDRho ε β Y - pDRho ε β Y * pDRho ε β X = pDRho ε β (X * Y - Y * X) := by
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, pDRho ε β Z = (adDFull Z).submatrix Subtype.val Subtype.val :=
    fun _ => rfl
  have hs : ∀ A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
      ((A - B).submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) =
        (A.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) -
          (B.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) := fun _ _ => rfl
  rw [e, e, e, ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hX i k hi hk),
    ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hY i k hi hk), ← hs, adDFull_bracket]

lemma prho_single_bracket (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pAdM_kRel : Formalism.REAL.KRel ε (pAdM ε β) := by
  intro a b c d hab hcd
  have e : ∀ a b, pAdM ε β a b = pDRho ε β (Matrix.single a b 1) := fun a b => (pDRho_single ε β a b).symm
  simp only [e]
  rw [pDRho_bracket ε β (single_mul_Jm hab 1) (single_mul_Jm hcd 1), prho_single_bracket]
  split_ifs <;> simp

theorem pRho_continuous :
    Continuous (fun k : KG ε =>
      ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) := by
  have hm : Continuous (fun k : KG ε => toMK k) := (continuous_toM ε).comp continuous_subtype_val
  refine continuous_matrix fun p q => ?_
  simp only [pRho_apply]
  exact (hm.matrix_elem _ _).mul ((hm.matrix_elem _ _).star)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma prho_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h := (L.hasFDerivAt).comp_hasDerivAt _ (hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ))
  have h2 := hasDerivAt_real_of_complex' (z := 0) h
  have e : L (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by simp [L]
  exact h2.congr_deriv e

end Deriv

theorem pRho_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (i j : pIdx ε β) :
    HasDerivAt (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
      (pDRho ε β X i j) 0 := by
  have hf : (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i.1.1 j.1.1 *
        star (NormedSpace.exp ((t : ℂ) • X) i.1.2 j.1.2) := by
    funext t
    rw [pRho_apply, hγ t]
  rw [hf]
  have h := (prho_entry_hasDerivAt X i.1.1 j.1.1).mul (prho_entry_hasDerivAt X i.1.2 j.1.2).star
  have hs : star (X i.1.2 j.1.2) = -X j.1.2 i.1.2 := by
    have := congrFun (congrFun (onep_skew hX) j.1.2) i.1.2
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have e : X i.1.1 j.1.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.2 j.1.2) +
      NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.1 j.1.1 * star (X i.1.2 j.1.2) = pDRho ε β X i j := by
    rw [pDRho_apply, hs]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  exact h.congr_deriv e

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pPlus_fst_ne_snd {ε : Fin n → Bool} {β : Bool} (p : pIdx ε β) : p.1.1 ≠ p.1.2 := by
  intro h
  obtain ⟨h1, h2⟩ := p.2
  rw [h] at h1
  rw [h1] at h2
  cases β <;> simp at h2

theorem pPlus_pAdM_diag (ε : Fin n → Bool) (β : Bool) (a : Fin n) :
    pAdM ε β a a = Matrix.diagonal fun p => ((pWt ε β p a : ℝ) : ℂ) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [pAdM, pWt, Pi.single_apply, Pi.sub_apply, Matrix.diagonal_apply_eq, and_true, and_self]
    by_cases h1 : p.1.1 = a <;> by_cases h2 : p.1.2 = a
    · exact absurd (h1.trans h2.symm) (pPlus_fst_ne_snd p)
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)]; simp
    · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm]; simp
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
  · rw [Matrix.diagonal_apply_ne _ hpq]
    have h1 : ¬ (p.1.1 = a ∧ q.1.1 = a ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext (h.1.trans h.2.1.symm) h.2.2))
    have h2 : ¬ (q.1.2 = a ∧ p.1.2 = a ∧ p.1.1 = q.1.1) := fun h =>
      hpq (Subtype.ext (Prod.ext h.2.2 (h.2.1.trans h.1.symm)))
    simp only [pAdM, if_neg h1, if_neg h2, sub_self]

theorem pPlus_pWt_injective (ε : Fin n → Bool) (β : Bool) : Function.Injective (pWt ε β) := by
  intro p q h
  have hp := pPlus_fst_ne_snd p
  have e1 := congrFun h p.1.1
  have e2 := congrFun h p.1.2
  simp only [pWt, Pi.sub_apply, Pi.single_apply] at e1 e2
  rw [if_pos trivial, if_neg hp] at e1
  rw [if_neg (Ne.symm hp), if_pos trivial] at e2
  have h1 : p.1.1 = q.1.1 := by
    by_contra hne
    rw [if_neg hne] at e1
    split_ifs at e1 <;> norm_num at e1
  have h2 : p.1.2 = q.1.2 := by
    by_contra hne
    rw [if_neg hne] at e2
    split_ifs at e2 <;> norm_num at e2
  exact Subtype.ext (Prod.ext h1 h2)

theorem pPlus_card_eq_one (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (p : pIdx ε β) :
    Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨p, rfl⟩, fun q => Subtype.ext (pPlus_pWt_injective ε β (add_left_cancel q.2).symm)⟩

theorem pPlus_of_parts (hcount : PieriCountStatement) (htens : TensHWStatement)
    (hkt : KTypeIntDomStatement) (hws : WeylSumPStatement)
    (hρ : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool),
      ∃ (ρ : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ))
        (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ),
        Continuous (fun k : KG ε =>
          ((ρ k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) ∧
        (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          ∀ i j, HasDerivAt (fun t : ℝ =>
            ((ρ (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
            (dρ X i j) 0) ∧
        ∀ a b, dρ (Matrix.single a b 1) = pAdM ε β a b)
    (hrel : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool), Formalism.REAL.KRel ε (pAdM ε β)) :
    PPlusStatement := by
  intro n ε β Λ T
  obtain ⟨ρ, dρ, hcont, hder, hsingle⟩ := hρ n ε β
  have hfun : (fun a b => dρ (Matrix.single a b 1)) = pAdM ε β := by
    funext a b
    exact hsingle a b
  obtain ⟨hint, hdom⟩ := hkt n ε Λ T
  obtain ⟨hsum, hvan⟩ := hws n ε β Λ hint hdom
  have hc := hcount n ε Λ T (pIdx ε β) ρ dρ (pWt ε β) hcont hder
    (by rw [hfun]; exact hrel n ε β)
    (fun a => by rw [hsingle]; exact pPlus_pAdM_diag ε β a) (pPlus_pWt_injective ε β)
    (by rw [hsum, Nat.card_eq_fintype_card]) hvan
  rw [hfun] at hc
  obtain ⟨hexist, hall⟩ := hc
  have ht := htens T.V n ε (kunits T) Λ T.w (pIdx ε β) (pAdM ε β) (pWt ε β) (KType.kRel T) (KType.kUnit T)
    (KType.kHighest_w T) (KType.kSpan_eq_top T) (hrel n ε β) (pPlus_pAdM_diag ε β)
  refine ⟨hall, fun p => ?_, hexist⟩
  calc Module.finrank ℂ (khwSub ε (tensAct (kunits T) (pAdM ε β)) (Λ + pWt ε β p))
      ≤ Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} := (ht.2 _).2
    _ = 1 := pPlus_card_eq_one ε β Λ p

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem pieriCount : PieriCountStatement := pieriCount_of compRed kRepRel

theorem pieriStd : PieriStdStatement := pieriStd_of compRed kRepRel

theorem pieriDual : PieriDualStatement := pieriDual_of compRed kRepRel

theorem pPlus : PPlusStatement :=
  pPlus_of_parts pieriCount tensHW kTypeIntDom weylSumP
    (fun _ ε β => ⟨pRho ε β, pDRho ε β, pRho_continuous ε β,
      fun X hX γ hγ i j => pRho_hasDerivAt ε β X hX γ hγ i j, fun a b => pDRho_single ε β a b⟩)
    (fun _ ε β => pAdM_kRel ε β)

end ReciprocityTheory.ChartRestriction.DS.HW
end
