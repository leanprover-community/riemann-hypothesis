import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CrLem
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LamTrace
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Crux
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmH

section
noncomputable section

open MeasureTheory Matrix Set
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def epsM (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem epsM_mul_self : epsM n * epsM n = 1 := by
  simp [epsM, fromBlocks_multiply, ← fromBlocks_one]

def epsU (n : ℕ) : GL (Fin n ⊕ Fin n) ℂ := ⟨epsM n, epsM n, epsM_mul_self, epsM_mul_self⟩

theorem eps_conj_blocks (M : M2 n) :
    epsM n * M * epsM n = fromBlocks M.toBlocks₁₁ (-M.toBlocks₁₂) (-M.toBlocks₂₁) M.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [epsM, fromBlocks_multiply]

theorem epsM_conjTranspose : (epsM n)ᴴ = epsM n := by
  simp [epsM, fromBlocks_conjTranspose]

theorem eps_JJ : epsM n * JJ n * epsM n = -JJ n := by
  simp [epsM, JJ, fromBlocks_multiply, fromBlocks_neg]

theorem inG_eps_conj {M : M2 n} (h : InG M) : InG (epsM n * M * epsM n) := by
  unfold InG at h ⊢
  have e4 : ∀ X : M2 n, epsM n * (JJ n * (epsM n * X)) = -(JJ n * X) := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, eps_JJ, Matrix.neg_mul]
  have h' : ∀ X : M2 n, Mᴴ * (JJ n * (M * X)) = JJ n * X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]
  simp only [conjTranspose_mul, epsM_conjTranspose, Matrix.mul_assoc]
  rw [e4, Matrix.mul_neg, Matrix.mul_neg, h', ← Matrix.mul_assoc, eps_JJ, neg_neg]

def cHom (n : ℕ) : GR n →* GR n where
  toFun y := ⟨epsU n * y.1 * epsU n, by
    show InG ((epsU n * y.1 * epsU n : GL (Fin n ⊕ Fin n) ℂ) : M2 n)
    simpa [epsU] using inG_eps_conj (n := n) y.2⟩
  map_one' := by
    ext : 2
    simp [epsU, epsM_mul_self]
  map_mul' x y := by
    ext : 2
    simp only [Subgroup.coe_mul, Units.val_mul]
    have h := epsM_mul_self (n := n)
    simp only [epsU, Units.val_mk]
    calc epsM n * (x.1.1 * y.1.1) * epsM n = epsM n * x.1.1 * (epsM n * epsM n) * y.1.1 * epsM n := by
          rw [h]; simp [Matrix.mul_assoc]
      _ = epsM n * x.1.1 * epsM n * (epsM n * y.1.1 * epsM n) := by simp [Matrix.mul_assoc]

theorem mR_c (y : GR n) : mR (cHom n y) = epsM n * mR y * epsM n := rfl

theorem cHom_cHom (y : GR n) : cHom n (cHom n y) = y := by
  apply Subtype.ext
  apply Units.ext
  show mR (cHom n (cHom n y)) = mR y
  rw [mR_c, mR_c]
  have h := epsM_mul_self (n := n)
  calc epsM n * (epsM n * mR y * epsM n) * epsM n = (epsM n * epsM n) * mR y * (epsM n * epsM n) := by
        simp only [Matrix.mul_assoc]
    _ = mR y := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem cHom_cont : Continuous (cHom n) := by
  show Continuous fun y : GR n => (⟨epsU n * y.1 * epsU n, _⟩ : GR n)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem first_cayley_block_of_conjugation (y : GR n) : u1 (mR (cHom n y)) = u2 (mR y) := by
  rw [mR_c, u1, u2, eps_conj_blocks]
  simp

theorem second_cayley_block_of_conjugation (y : GR n) : u2 (mR (cHom n y)) = u1 (mR y) := by
  rw [mR_c, eps_conj_blocks]
  simp [u1, u2]

theorem det_c (y : GR n) : (mR (cHom n y)).det = (mR y).det := by
  have h := congrArg Matrix.det (epsM_mul_self (n := n))
  rw [det_mul, det_one] at h
  rw [mR_c, det_mul, det_mul]
  calc (epsM n).det * (mR y).det * (epsM n).det = (mR y).det * ((epsM n).det * (epsM n).det) := by ring
    _ = (mR y).det := by rw [h, mul_one]

theorem spherical_section_conjugation_swap (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e (cHom n y) = F0 q p e y := by
  simp only [F0, f0, det_c, first_cayley_block_of_conjugation, second_cayley_block_of_conjugation]
  ring

theorem norm_sq_det_cayley_blocks_eq (M : M2 n) (h : InG M) : ‖(u1 M).det‖ ^ 2 = ‖(u2 M).det‖ ^ 2 := by
  have hJ2 : JJ n * JJ n = -1 := by
    simp only [JJ, fromBlocks_multiply]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  unfold InG at h
  have hL : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    calc -(JJ n * Mᴴ * JJ n) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, hJ2, neg_neg]
  have hR : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 hL
  have hMJ : M * JJ n * Mᴴ = JJ n := by
    calc M * JJ n * Mᴴ = M * (-(JJ n * Mᴴ * JJ n)) * JJ n := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ2, Matrix.mul_one, neg_neg]
      _ = JJ n := by rw [hR, Matrix.one_mul]
  have hM : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (fromBlocks_toBlocks M).symm
  rw [hM] at hMJ
  have hb := congrArg toBlocks₂₂ hMJ
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at hb
  have key : M.toBlocks₂₁ * (M.toBlocks₂₂)ᴴ = M.toBlocks₂₂ * (M.toBlocks₂₁)ᴴ := by
    rw [← sub_eq_zero, ← hb]
    abel
  have e1 : u1 M * (u1 M)ᴴ = u2 M * (u2 M)ᴴ := by
    simp [u1, u2, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, key]
    abel
  have hn : ∀ u : Matrix (Fin n) (Fin n) ℂ, ((‖u.det‖ ^ 2 : ℝ) : ℂ) = (u * uᴴ).det := by
    intro u
    simp [det_mul, det_conjTranspose, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  rw [hn, hn, e1]

theorem hLoc_c (y : GR n) : hLoc (cHom n y) = hLoc y := by
  simp only [hLoc, first_cayley_block_of_conjugation]
  rw [norm_sq_det_cayley_blocks_eq (mR y) y.2]

theorem zkey (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a - b) = -((Complex.I • a + b)ᴴ * (-(Complex.I • c) + d)) := by
  rw [eq_neg_iff_add_eq_zero]
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have h1 : aᴴ * c = cᴴ * a := sub_eq_zero.1 E1
  have h3 : bᴴ * d = dᴴ * b := sub_eq_zero.1 E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  abel

private theorem eq_zero_of_star_dotProduct_self_eq_zero (v : Fin n → ℂ) (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have e : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    simp [dotProduct, Complex.conj_mul']
  rw [e] at h
  have h' : ∑ i, ‖v i‖ ^ 2 = 0 := by exact_mod_cast h
  have h'' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).1 h'
  funext i
  simpa using h'' i (Finset.mem_univ i)

private theorem card_fromBlocks_cayley_eq_mul (M : M2 n) (h : InG M) :
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₁) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₁ = 0 ∧
    -((M.toBlocks₂₁)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₁)ᴴ * M.toBlocks₂₂ = 1 ∧
    -((M.toBlocks₂₂)ᴴ * M.toBlocks₁₂) + (M.toBlocks₁₂)ᴴ * M.toBlocks₂₂ = 0 := by
  have hM := (fromBlocks_toBlocks M).symm
  unfold InG at h
  rw [hM] at h
  have h11 := congrArg toBlocks₁₁ h
  have h12 := congrArg toBlocks₁₂ h
  have h22 := congrArg toBlocks₂₂ h
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h11 h12 h22
  exact ⟨h11, h12, h22⟩

private theorem conjTranspose_I_smul_add_sub_eq_two_I (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : -(cᴴ * a) + aᴴ * c = 0)
    (E2 : -(cᴴ * b) + aᴴ * d = 1) (E3 : -(dᴴ * b) + bᴴ * d = 0) :
    (Complex.I • c + d)ᴴ * (Complex.I • a + b) - (Complex.I • a + b)ᴴ * (Complex.I • c + d) =
      (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have := congrArg conjTranspose E2
    simp [conjTranspose_add, conjTranspose_neg, conjTranspose_mul] at this
    rw [sub_eq_neg_add]
    exact this
  have h1 : aᴴ * c = cᴴ * a := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E1
  have h3 : bᴴ * d = dᴴ * b := by
    rw [← sub_eq_zero, sub_eq_neg_add]
    exact E3
  have h2 : aᴴ * d = 1 + cᴴ * b := by
    rw [← E2]
    abel
  have h4 : dᴴ * a = 1 + bᴴ * c := by
    rw [← E2']
    abel
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h1, h3, h2, h4]
  simp only [smul_add]
  module

private theorem det_u1_ne_zero_of_inG (M : M2 n) (h : InG M) : (u1 M).det ≠ 0 := by
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul M h
  intro hdet
  obtain ⟨v, hv, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have W := conjTranspose_I_smul_add_sub_eq_two_I _ _ _ _ h11 h12 h22
  have hu' : (Complex.I • M.toBlocks₂₁ + M.toBlocks₂₂) *ᵥ v = 0 := hu
  have hz : star v ⬝ᵥ (((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) = 0 := by
    rw [← W, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu',
      Matrix.mulVec_zero, dotProduct_zero, sub_zero, dotProduct_mulVec, ← star_mulVec, hu', star_zero,
      zero_dotProduct]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at hz
  rcases hz with h0 | h0
  · simp [Complex.I_ne_zero] at h0
  · exact hv (eq_zero_of_star_dotProduct_self_eq_zero v h0)

private theorem det_u2_ne_zero_of_inG (M : M2 n) (h : InG M) : (u2 M).det ≠ 0 := by
  have e : u2 M = u1 (epsM n * M * epsM n) := by
    rw [u1, u2, eps_conj_blocks]
    simp
  rw [e]
  exact det_u1_ne_zero_of_inG _ (inG_eps_conj h)

theorem zOf_c (y : GR n) : zOf (cHom n y) = -(zOf y)ᴴ := by
  have hy : InG (mR y) := y.2
  obtain ⟨h11, h12, h22⟩ := card_fromBlocks_cayley_eq_mul (mR y) hy
  have hU1 := det_u1_ne_zero_of_inG (mR y) hy
  have hU2 := det_u2_ne_zero_of_inG (mR y) hy
  have zk := zkey (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ (mR y).toBlocks₂₁ (mR y).toBlocks₂₂
    (by rw [sub_eq_neg_add]; exact h11) (by rw [sub_eq_neg_add]; exact h12)
    (by rw [sub_eq_neg_add]; exact h22)
  simp only [zOf, first_cayley_block_of_conjugation]
  rw [mR_c, eps_conj_blocks]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
  rw [conjTranspose_mul, conjTranspose_nonsing_inv]
  have hU1h : IsUnit ((u1 (mR y))ᴴ).det := by
    rw [det_conjTranspose]
    exact (isUnit_iff_ne_zero.2 hU1).star
  have hU2' : IsUnit (u2 (mR y)).det := isUnit_iff_ne_zero.2 hU2
  have zk' : (u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) =
      -((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y)) := by
    rw [← sub_eq_add_neg]
    exact zk
  calc (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂) * (u2 (mR y))⁻¹
      = ((u1 (mR y))ᴴ)⁻¹ * ((u1 (mR y))ᴴ * (Complex.I • (mR y).toBlocks₁₁ + -(mR y).toBlocks₁₂)) *
          (u2 (mR y))⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU1h, Matrix.one_mul]
    _ = ((u1 (mR y))ᴴ)⁻¹ * (-((Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ * u2 (mR y))) *
          (u2 (mR y))⁻¹ := by rw [zk']
    _ = -(((u1 (mR y))ᴴ)⁻¹ * (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂)ᴴ) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hU2', Matrix.mul_one]

theorem herm_neg (x : Fin n → Fin n → ℝ) : herm (-x) = -herm x := by
  ext i j
  simp [herm]
  ring

theorem eps_nU (B : Matrix (Fin n) (Fin n) ℂ) : epsM n * nU B * epsM n = nU (-B) := by
  rw [eps_conj_blocks]
  simp [nU]

theorem singTest_neg {ψ : (Fin n → Fin n → ℝ) → ℂ} (h : IsSingTest ψ) : IsSingTest (fun x => ψ (-x)) := by
  refine ⟨h.1.comp continuous_neg, h.2.1.comp_homeomorph (Homeomorph.neg _), fun β hβ hdet => ?_⟩
  have e : ∀ x, eTr β x = eTr (-β) (-x) := by
    intro x
    simp [eTr, herm_neg]
  simp_rw [e]
  rw [integral_neg_eq_self (fun x => ψ x * eTr (-β) x) volume]
  exact h.2.2 (-β) hβ.neg (by rw [det_neg, hdet, mul_zero])

theorem conj : Conj := by
  intro hh m n p q e hm hmn hpq G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq] at hf
    rw [hp, hq]
    exact hh m n e hm hmn G Pp Γ ι s₀ Ht f hι hf U d Ê t hU hR hs hD hC hE j hj hsing g
  · rw [hp, hq] at hf
    rw [hp, hq]
    have hm0 : m ≠ 0 := by omega
    have hf' : ∀ g' : G, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g' = x * (ι.comp (cHom n)) y ∧
        ∀ y' : GR n, ((Ht (x * (ι.comp (cHom n)) y') : ℝ) = r * hLoc y' ∧
          f (x * (ι.comp (cHom n)) y') = S * F0 m 0 e y') := by
      intro g'
      obtain ⟨x, y, S, r, hr, hg, hy⟩ := hf g'
      refine ⟨x, cHom n y, S, r, hr, ?_, fun y' => ?_⟩
      · simp [hg, cHom_cHom]
      · obtain ⟨h1, h2⟩ := hy (cHom n y')
        refine ⟨?_, ?_⟩
        · simpa [hLoc_c] using h1
        · simpa [spherical_section_conjugation_swap] using h2
    have hs' : ∀ ψ : (Fin n → Fin n → ℝ) → ℂ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n,
        (∀ x, mR (nb x) = nU (herm x)) → ∀ (g' : G) (a b : GR n),
          ∫ x, iteratedDeriv j (fun s => Ê s (g' * (ι.comp (cHom n)) (a * nb x * b))) s₀ * ψ x = 0 := by
      intro ψ hψ nb hnb g' a b
      have hnb' : ∀ x, mR (cHom n (nb (-x))) = nU (herm x) := by
        intro x
        rw [mR_c, hnb, herm_neg, eps_nU, neg_neg]
      have h0 := hsing (fun x => ψ (-x)) (singTest_neg hψ) (fun x => cHom n (nb (-x))) hnb' g'
        (cHom n a) (cHom n b)
      rw [← integral_neg_eq_self]
      simpa [map_mul] using h0
    obtain ⟨H, hH, hrep⟩ := hh m n e hm hmn G Pp Γ (ι.comp (cHom n)) s₀ Ht f (hι.comp cHom_cont) hf' U d Ê t
      hU hR hs hD hC hE j hj hs' g
    refine ⟨H, hH, fun y => ?_⟩
    have h1 := hrep (cHom n y)
    simp only [MonoidHom.comp_apply, cHom_cHom, spherical_section_conjugation_swap, zOf_c] at h1
    show iteratedDeriv j (fun x => Ê x (g * ι y)) s₀ = _
    rw [h1]
    simp [hm0]

end PositivityTheory.Rg.Sw.HSt
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem inner_gen (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hd : Q.det = 0) :
    ∫ s, ψ s * Complex.exp (Complex.I * ((herm s)ᵀ * Q).trace) = 0 := by
  obtain ⟨_, _, h⟩ := hψ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  have hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hQ.transpose.eq]
    congr 1
    simp [Complex.conj_ofReal]
  have hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]
  have key := h _ hβH hβd
  rw [← key]
  congr 1
  ext s
  simp only [eTr]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]
  field_simp

open PositivityTheory.Rg.Sw.WR.G.GM in
theorem core2 (hmn : m < n) (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (H0 : Matrix (Fin n) (Fin n) ℂ)
    (hH : H0.IsHermitian) (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = 0 := by
  have hψ0 := hψ
  obtain ⟨hψc, hψs, -⟩ := hψ0
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRRh : (R⁻¹)ᴴ * Rᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]
  have hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian := by
    intro s
    have h := Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0 := by
    intro s
    have h := GM.det_ne_zero (hBH s) 1
    simpa using h
  have hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) =
      R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ := by
    intro s
    have hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s := by
      simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRRh, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) =
      ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m := by
    intro s
    have hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a =
        (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ := by
      intro a
      simp [Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]
    rw [base m n _ 1 1 one_pos _ (hBH s)]
    simp only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdR : R.det ≠ 0 := hR.ne_zero
  have hdRh : Rᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hdR
  have hπ : (Real.pi : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 →
      Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m) := by
    intro P D A B Y hP hD' hA' hB'
    have k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D) := by
      field_simp
    rw [k, mul_pow]
    ring
  have hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m =
      ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m *
        (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) := by
    intro s
    rw [hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]
    exact halg _ _ _ _ _ hπ (hD s) hdR hdRh
  have hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume :=
    integP m n 1 one_pos 1
  have hψi : Integrable ψ volume := hψc.integrable_of_hasCompactSupport hψs
  have hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) =>
      ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)))
      (volume.prod volume) := by
    refine Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) =>
          R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2 :=
        ((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul
          continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)
      exact (hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul
        ((GI.continuous_gs 1).comp continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))
    · refine Filter.Eventually.of_forall fun p => le_of_eq ?_
      obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [GM.norm_phase (hBH s) x, mul_one]
  have hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0 := by
    intro x
    have hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose
    have hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0 := by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]
    have htr : ∀ s : Fin n → Fin n → ℝ,
        (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace +
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace := by
      intro s
      have h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm R⁻¹]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.add_mul, Matrix.trace_add]
      congr 1
      rw [← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]
    have hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) =
        (evX (1 : PX m n) x * gs 1 x *
          Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace)) *
        (ψ s * Complex.exp (Complex.I *
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace)) := by
      intro s
      rw [htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]
      ring
    simp only [hrw]
    rw [integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]
  have hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0 := by
    simp only [secN]
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    simp only [hin, integral_zero]
  simp only [hpt]
  rw [integral_const_mul, hmain, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def v1 (b : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • b.toBlocks₁₁ + b.toBlocks₁₂

theorem fz_zero (e : ℤ) (x : M2 n) : fz m e 0 x = x.det ^ e * (u1 x).det ^ (-(m : ℤ)) := by
  simp [fz]

theorem blocks_mul (g b : M2 n) : (g * b).toBlocks₂₁ = g.toBlocks₂₁ * b.toBlocks₁₁ + g.toBlocks₂₂ * b.toBlocks₂₁ ∧
    (g * b).toBlocks₂₂ = g.toBlocks₂₁ * b.toBlocks₁₂ + g.toBlocks₂₂ * b.toBlocks₂₂ := by
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.add_apply]

theorem second_coord_mul_inner (g b : M2 n) : u1 (g * b) = g.toBlocks₂₁ * v1 b + g.toBlocks₂₂ * u1 b := by
  obtain ⟨h1, h2⟩ := blocks_mul g b
  simp only [u1, v1, h1, h2, Matrix.mul_add, Matrix.mul_smul, smul_add]
  abel

theorem nU_blocks (y : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) :
    (y * nU S).toBlocks₂₁ = y.toBlocks₂₁ ∧ (y * nU S).toBlocks₂₂ = y.toBlocks₂₁ * S + y.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := blocks_mul y (nU S)
  simp only [nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem det_nU (S : Matrix (Fin n) (Fin n) ℂ) : (nU S).det = 1 := by
  simp [nU]

private theorem mul_JJ_mul_conjTranspose_eq_of_inG (y : M2 n) (hy : InG y) : y * JJ n * yᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := by
    ext (i|i) (j|j) <;> simp [JJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hy' : yᴴ * JJ n * y = JJ n := hy
  have h1 : (-(JJ n * yᴴ * JJ n)) * y = 1 := by
    calc (-(JJ n * yᴴ * JJ n)) * y = -(JJ n * (yᴴ * JJ n * y)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJ, neg_neg]
  have h2 : y * (-(JJ n * yᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc y * JJ n * yᴴ = y * JJ n * yᴴ * (-(JJ n * JJ n)) := by rw [hJ, neg_neg, Matrix.mul_one]
    _ = (y * (-(JJ n * yᴴ * JJ n))) * JJ n := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [h2, Matrix.one_mul]

theorem hermit_cd (y : M2 n) (hy : InG y) (hc : IsUnit y.toBlocks₂₁.det) :
    (y.toBlocks₂₁⁻¹ * y.toBlocks₂₂).IsHermitian := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_mul_conjTranspose_eq_of_inG y hy)
  rw [← Matrix.fromBlocks_toBlocks y] at h
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at h
  rw [neg_add_eq_zero] at h
  have hcH : IsUnit (y.toBlocks₂₁)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hc
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc (y.toBlocks₂₂)ᴴ * (y.toBlocks₂₁)ᴴ⁻¹
      = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₁ * (y.toBlocks₂₂)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
    _ = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₂ * (y.toBlocks₂₁)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by rw [← h]
    _ = (y.toBlocks₂₁)⁻¹ * y.toBlocks₂₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcH, Matrix.mul_one]

theorem v_rel (b : M2 n) (hb : InG b) : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e := hb
  unfold InG at e
  rw [← Matrix.fromBlocks_toBlocks b] at e
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  have key : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b =
      -(-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₁)
      - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₂)
      + Complex.I • ((-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₂)
        - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₁)) := by
    simp only [u1, v1, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]
    match_scalars <;>
      first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
  rw [key, e1, e2, e3, e4]
  module

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain (b : M2 n) (hb : InG b) : IsUnit (u1 b).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hr := congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub,
    dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct,
    sub_zero, Matrix.zero_vecMul] at hr
  simp [Matrix.vecMul_smul] at hr
  have h2 : ∑ j, Complex.normSq (x j) = 0 := by
    have h3 := congrArg Complex.re hr
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _] at h2
  apply hx0
  funext j
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

theorem factor (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det) :
    ∃ (R H0 : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ), IsUnit R.det ∧ H0.IsHermitian ∧ κ ≠ 0 ∧
      ∀ S, (u1 (y * nU S * b)).det = κ * (R * Rᴴ - Complex.I • (H0 + S)).det := by
  have hU := exists_unitary_mul_blockTriangular_of_inFlagDomain b hb
  have hH := hermit_cd y hy hc
  obtain ⟨U, hUdef⟩ : ∃ U, U = u1 b := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = v1 b := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹ := ⟨_, rfl⟩
  have hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hUdef, hVdef]
    exact v_rel b hb
  rw [← hUdef] at hU
  rw [← hCdef] at hc
  rw [← hCdef, ← hDdef] at hH
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hUU' : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]
  have hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
    calc P - Pᴴ = ((U⁻¹)ᴴ * Uᴴ) * V * U⁻¹ - (U⁻¹)ᴴ * Vᴴ * (U * U⁻¹) := by
          rw [hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]
      _ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
          rw [hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ) := by
    rw [hRR, hP, smul_smul]
    congr 1
    ring
  refine ⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)
  · refine Matrix.IsHermitian.add ?_ hH
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · exact mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero
  · intro S
    have hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))
        = P + C⁻¹ * D + S := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, hI]
      module
    have e1 : C * P * U = C * V := by
      rw [hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    have e2 : C * (C⁻¹ * D) * U = D * U := by
      rw [← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]
    have hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ
        - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U := by
      rw [hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      rw [e1, e2]
      abel
    rw [hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
    ring

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  rw [← Matrix.fromBlocks_toBlocks x] at hx'
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hx'
  simp at hx'
  obtain ⟨h1, h2, h3, h4⟩ := hx'
  have hu : u1 x = Complex.I • x.toBlocks₂₁ + x.toBlocks₂₂ := rfl
  rw [hu]
  set A := x.toBlocks₁₁
  set B := x.toBlocks₁₂
  set C := x.toBlocks₂₁
  set D := x.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h1)
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = Dᴴ * A + -1 := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h4)
  have key : (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [e1, e2, e3, e4]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  intro h0
  obtain ⟨v, hv, huv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have hs : star v ᵥ* (Complex.I • C + D)ᴴ = 0 := by
    rw [← Matrix.star_mulVec, huv, star_zero]
  have hz : star v ⬝ᵥ (((Complex.I • A + B)ᴴ * (Complex.I • C + D)
      - (Complex.I • C + D)ᴴ * (Complex.I • A + B)) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv,
      Matrix.mulVec_zero, dotProduct_zero, Matrix.dotProduct_mulVec, hs, zero_dotProduct, sub_zero]
  rw [key, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hz
  have h2I : (-2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  open ComplexOrder in
  exact hv (dotProduct_star_self_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left h2I))

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology Polynomial

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem eventually_unit (y : M2 n) (hy : InG y) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (y * nbar t).toBlocks₂₁.det := by
  set C := y.toBlocks₂₁ with hC
  set D := y.toBlocks₂₂ with hD
  let M : Matrix (Fin n) (Fin n) ℂ[X] := C.map Polynomial.C + (Polynomial.X : ℂ[X]) • D.map Polynomial.C
  have hev : ∀ z : ℂ, (M.det).eval z = (C + z • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    have h1 := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero] at h1
    have hu : u1 y = Complex.I • C + D := rfl
    have hmat : C + (-Complex.I) • D = (-Complex.I) • u1 y := by
      rw [hu, smul_add, smul_smul]
      simp
    rw [hmat, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (det_first_cayley_block_ne_group y hy)) h1.symm
  have hfin : {t : ℝ | (M.det).eval (t : ℂ) = 0}.Finite := by
    refine ((M.det.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact ht
  have hS : IsClosed ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnhds : ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    hS.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ht ht0
  rw [nbar_block, ← hev]
  exact isUnit_iff_ne_zero.2 (fun h => ht ⟨h, ht0⟩)

private theorem inG_mul' {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

private theorem inG_nU_herm' (s : Fin n → Fin n → ℝ) : InG (nU (herm s)) := by
  have hh : (herm s)ᴴ = herm s := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add, map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hh]

theorem vanish_all (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  let G : ℝ → (Fin n → Fin n → ℝ) → ℂ := fun t s => fz m e 0 (y * nbar t * nU (herm s) * b) * ψ s
  let X : ℝ × (Fin n → Fin n → ℝ) → M2 n := fun p => y * nbar p.1 * nU (herm p.2) * b
  have hIn : ∀ p, InG (X p) := fun p =>
    inG_mul' (inG_mul' (inG_mul' hy (inG_nbar p.1)) (inG_nU_herm' p.2)) hb
  have h1 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nbar (n := n) p.1 := by
    unfold nbar
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const) continuous_const
  have h2 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nU (herm p.2) := by
    unfold nU
    refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
    unfold herm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fun_prop
  have hX : Continuous X :=
    ((continuous_const.matrix_mul h1).matrix_mul h2).matrix_mul continuous_const
  have hU : Continuous fun p => u1 (X p) := by
    unfold u1
    refine (Continuous.const_smul ?_ Complex.I).add ?_ <;>
      exact continuous_pi fun i => continuous_pi fun j => hX.matrix_elem _ _
  have hcont : Continuous (Function.uncurry G) := by
    have hG : Function.uncurry G = fun p => (X p).det ^ e * (u1 (X p)).det ^ (-(m : ℤ)) * ψ p.2 := by
      funext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, X, fz_zero]
    rw [hG]
    exact ((hX.matrix_det.zpow₀ e fun p => Or.inl (det_ne_of_inG _ (hIn p))).mul
      (hU.matrix_det.zpow₀ _ fun p => Or.inl (det_first_cayley_block_ne_group _ (hIn p)))).mul (hψ.1.comp continuous_snd)
  have hK : IsCompact (tsupport ψ) := hψ.2.1
  have hInt : ∀ t, ∫ s, G t s = ∫ s in tsupport ψ, G t s := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun s hs => by simp [G, image_eq_zero_of_notMem_tsupport hs])).symm
  have hc : Continuous fun t => ∫ s in tsupport ψ, G t s :=
    continuous_parametric_integral_of_continuous hcont hK
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ s in tsupport ψ, G t s = 0 := by
    filter_upwards [eventually_unit y hy] with t ht
    rw [← hInt]
    exact vanish_inv hmn e (y * nbar t) b (inG_mul' hy (inG_nbar t)) hb ht ψ hψ
  have hlim : Tendsto (fun t => ∫ s in tsupport ψ, G t s) (𝓝[≠] 0) (𝓝 (∫ s in tsupport ψ, G 0 s)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : ∫ s in tsupport ψ, G 0 s = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  have hn0 : nbar (n := n) 0 = 1 := by simp [nbar]
  have := (hInt 0).trans h0
  simpa [G, hn0] using this

end PositivityTheory.Rg.Sw.HSt.L3
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

theorem lt3 : SingularTestsKillVacuum := by
  intro n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ ha hb hx
  have mulG : ∀ {p q : M2 n}, InG p → InG q → InG (p * q) := by
    intro p q hp hq
    unfold InG at *
    calc (p * q)ᴴ * JJ n * (p * q) = qᴴ * (pᴴ * JJ n * p) * q := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hp, hq]
  have hG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have h : ∀ k, ∫ t, fz m e 0 (x * ι k * a * nU (herm t) * b) * ψ t = 0 := fun k =>
    L3.vanish_all hmn e _ b (mulG (mulG hx (hG k)) ha) hb ψ hψ
  simp only [tOp, h, mul_zero, integral_zero]

end PositivityTheory.Rg.Sw.HSt
end
end

section
namespace PositivityTheory.Rg.Sw.HSt

theorem locTau : LocTau := asmLT lt1 lt2 lt3 crux

end PositivityTheory.Rg.Sw.HSt
end

section
namespace PositivityTheory.Rg.Sw.HSt

theorem holLeadB : PositivityTheory.SiegelWeilFormula.HolLead := conj (asmH locTau secFz crLem)

end PositivityTheory.Rg.Sw.HSt
end
