import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FdPointAssembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.FdFjNearSup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.FdUnipMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalChartNormControlHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalShortVectorBoundOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Transference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Hf_unitary (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
    (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)
    (hx : x ∈ X.dom) (y w : Fin r → ℂ) :
    X.Hf (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g y) (Matrix.mulVec g w) = X.Hf x τ y w := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = g.mulVec (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    ext a b
    simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hcol, hg]
  have hppos : X.ppos (X.lmulC (fun _ => g) x) τ (g.mulVec y) = g.mulVec (X.ppos x τ y) := by
    simp only [Data.ppos, hcol, hgram, hg, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hlin : (2 : ℂ) • g.mulVec (X.ppos x τ y) - g.mulVec y =
      g.mulVec ((2 : ℂ) • X.ppos x τ y - y) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Data.Hf]
  rw [hppos, hlin, hg]

lemma ppos_mat_eq {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v : Fin r → ℂ) :
    X.ppos x τ v = X.ppos x' τ v := by
  simp only [Data.ppos, Data.gramPos, h]

lemma Hf_mat_eq {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v w : Fin r → ℂ) :
    X.Hf x τ v w = X.Hf x' τ v w := by
  simp only [Data.Hf, ppos_mat_eq X h]

lemma mat_lmulC_at (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.lmulC n x) τ = mat (X.lmulC (fun _ => n τ) x) τ := rfl

lemma majorant_bound_orthogonal_part (ξ : Fin r → E) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ)
    (hδ : ∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ))
    (τ : X.Ψ) (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w (emb τ.1 ξ) = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ (emb τ.1 ξ)) = 0) :
    X.maj x τ (δ τ w • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ w := by
  classical
  let u : X.Ψ → Fin r → ℂ := fun τ' => if τ' = τ then w else 0
  have hu : u ∈ X.Uz x ξ := by
    refine ⟨fun τ' => ?_, fun τ' => ?_⟩
    · by_cases h : τ' = τ
      · subst h
        simp [u, hw1]
      · simp [u, h, hC_zero_left]
    · by_cases h : τ' = τ
      · subst h
        have hsm : hermC τ'.1 X.Gm (X.Jz x u τ') (emb τ'.1 ξ) =
            I * hermC τ'.1 X.Gm (X.Jp x τ' w) (emb τ'.1 ξ) := by
          simp [Data.Jz, Data.Jp, u, hermC, Finset.mul_sum, mul_assoc]
        rw [hsm, X.Jp_adj hx τ' w (emb τ'.1 ξ), hw2, mul_zero]
      · simp [Data.Jz, u, h, X.ppos_zero, hC_zero_left]
  have hmain := hδ u hu τ
  simpa [u] using hmain

set_option maxHeartbeats 1000000 in
theorem unipotent_majorant_bound_data : ReducedFrameDomainCovering (E := E) := by
  intro r X ξ hξ x hx δ κ hκ0 hκ1 hδ
  have hCsub : ∀ (τ : X.Ψ) (u v w : Fin r → ℂ) (c : ℂ),
      hermC τ.1 X.Gm (u - c • v) w = hermC τ.1 X.Gm u w - c * hermC τ.1 X.Gm v w := by
    intro τ u v w c
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_assoc]
  have hCsmul : ∀ (τ : X.Ψ) (u w : Fin r → ℂ) (c : ℂ),
      hermC τ.1 X.Gm (c • u) w = c * hermC τ.1 X.Gm u w := by
    intro τ u w c
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := by
    intro τ
    have h : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
      simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
    rw [h, hξ.2.1, map_zero]
  have he0 : ∀ τ : X.Ψ, emb τ.1 ξ ≠ 0 := by
    intro τ h
    apply hξ.2.2
    funext a
    have h1 := congrFun h a
    simpa [Data.emb] using h1
  have hq : ∀ τ : X.Ψ, X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) = (X.maj x τ (emb τ.1 ξ) : ℂ) :=
    fun τ => X.Hf_self hx τ _
  have hqne : ∀ τ : X.Ψ, X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) ≠ 0 := by
    intro τ
    rw [hq τ]
    exact_mod_cast (X.maj_pos hx τ (he0 τ)).ne'
  have hHfJ : ∀ τ v, X.Hf x τ v (emb τ.1 ξ) = hermC τ.1 X.Gm v (X.Jp x τ (emb τ.1 ξ)) :=
    fun τ v => by rw [X.Hf_eq x hx]; rfl
  set N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => X.d2n x τ (emb τ.1 ξ) (δ τ) with hN
  have hqr : ∀ τ : X.Ψ, conj (X.d2q x τ (emb τ.1 ξ)) = X.d2q x τ (emb τ.1 ξ) := by
    intro τ
    show conj (X.Hf x τ _ _) = X.Hf x τ _ _
    rw [hq τ]
    exact Complex.conj_ofReal _
  have hU : ∀ τ u w, hermC τ.1 X.Gm ((N τ).mulVec u) ((N τ).mulVec w) = hermC τ.1 X.Gm u w :=
    fun τ u w => X.unipotent_transform_unitary (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) (hqr τ) u w
  have hNe : ∀ τ, (N τ).mulVec (emb τ.1 ξ) = emb τ.1 ξ :=
    fun τ => X.unipotent_fixes_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ)
  have hHfN : ∀ τ v w, X.Hf (X.lmulC N x) τ ((N τ).mulVec v) ((N τ).mulVec w) = X.Hf x τ v w :=
    fun τ v w => by
      rw [X.Hf_mat_eq (X.mat_lmulC_at N x τ)]
      exact X.Hf_unitary x τ (N τ) (hU τ) hx v w
  have hπsub : ∀ τ v (c : ℂ),
      X.d2pi x τ (emb τ.1 ξ) (v - c • emb τ.1 ξ) = X.d2pi x τ (emb τ.1 ξ) v := by
    intro τ v c
    have hJ : hermC τ.1 X.Gm (emb τ.1 ξ) (X.Jp x τ (emb τ.1 ξ)) = X.d2q x τ (emb τ.1 ξ) :=
      (hHfJ τ _).symm
    have hq0 : X.d2q x τ (emb τ.1 ξ) ≠ 0 := hqne τ
    rw [X.hyperbolic_projection_apply, X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, X.hyperbolic_coeff_b_apply,
      hCsub, hCsub, hee τ, hJ]
    ext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hπsmul : ∀ τ v (c : ℂ),
      X.d2pi x τ (emb τ.1 ξ) (c • v) = c • X.d2pi x τ (emb τ.1 ξ) v := by
    intro τ v c
    rw [X.hyperbolic_projection_apply, X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, X.hyperbolic_coeff_b_apply,
      hCsmul, hCsmul]
    ext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hNinv : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      (N τ).mulVec (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) = v := by
    intro τ v hv
    have hperp : hermC τ.1 X.Gm (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) (emb τ.1 ξ) = 0 := by
      rw [hCsub, hv, hee τ, mul_zero, sub_zero]
    rw [X.unipotent_on_orthogonal_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hperp, hπsub]
    simp
  have hHfperp : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf (X.lmulC N x) τ v (emb τ.1 ξ) = X.Hf x τ v (emb τ.1 ξ) -
        δ τ (X.d2pi x τ (emb τ.1 ξ) v) * X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) := by
    intro τ v hv
    have h1 := hHfN τ (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) (emb τ.1 ξ)
    rw [hNinv τ v hv, hNe τ] at h1
    rw [h1, X.Hf_eq x hx, X.Hf_eq x hx, X.Hf_eq x hx, hCsub]
  have hHfee : ∀ τ, X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ) =
      X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) := by
    intro τ
    have h1 := hHfN τ (emb τ.1 ξ) (emb τ.1 ξ)
    rwa [hNe τ] at h1
  have huz : ∀ u ∈ X.Uz x ξ, ∀ τ, hermC τ.1 X.Gm (u τ) (X.Jp x τ (emb τ.1 ξ)) = 0 := by
    intro u hu τ
    have h2 := hu.2 τ
    have hsm : X.Jz x u τ = I • X.Jp x τ (u τ) := rfl
    rw [hsm, hCsmul] at h2
    have h3 : hermC τ.1 X.Gm (X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 :=
      (mul_eq_zero.1 h2).resolve_left Complex.I_ne_zero
    rwa [X.Jp_adj hx] at h3
  have hπperp : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.d2pi x τ (emb τ.1 ξ) v = v - (X.Hf x τ v (emb τ.1 ξ) /
        X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ := by
    intro τ v hv
    rw [X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, hv, mul_zero, zero_smul, sub_zero, hHfJ τ v,
      div_eq_inv_mul]
    rfl
  have hdom : X.lmulC N x ∈ X.dom := by
    show ∀ τ : X.Ψ, (mat (X.lmulC N x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.lmulC N x) τ i).re
    intro τ
    have hm : mat (X.lmulC N x) τ = N τ * mat x τ := rfl
    have hcol : ∀ c, col (N τ * mat x τ) c = (N τ).mulVec (col (mat x τ) c) := by
      intro c
      funext k
      simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hgram : gram τ.1 X.Gm (N τ * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [gram, Matrix.of_apply, hcol, hU]
    refine ⟨?_, fun i => ?_⟩
    · rw [hm, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro hdet
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      apply hv0
      have horth : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by
        rw [← hU τ v w, hv, hC_zero_left]
      have hvm : Matrix.vecMul v (X.Gm.map τ.1) = 0 := by
        funext b
        have h1 := horth (Pi.single b 1)
        simpa [hermC, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
      exact Matrix.eq_zero_of_vecMul_eq_zero (map_det_ne τ.1 X.Gm X.Gm_det) hvm
    · simp only [dmin, hm, hgram]
      exact (hx τ).2 i
  refine ⟨N, hU, hNe, ?_, hdom, ?_, ?_, ?_, ?_⟩
  · intro u hu
    funext τ
    simp only [Data.applyV, Data.lineV, Pi.add_apply]
    exact X.unipotent_on_hyperbolic_complement (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) (hu.1 τ) (huz u hu τ)
  · intro u hu
    funext τ
    simp only [Data.aproj, Data.lineV, Pi.sub_apply, Data.ucomp]
    rw [hHfperp τ (u τ) (hu τ), hHfee τ, hπperp τ (u τ) (hu τ), ← sub_smul]
    congr 1
    field_simp [hqne τ]
  · intro τ
    have h1 : (X.maj (X.lmulC N x) τ (emb τ.1 ξ) : ℂ) = X.maj x τ (emb τ.1 ξ) := by
      rw [← X.Hf_self hdom τ, ← X.Hf_self hx τ, hHfee τ]
    exact_mod_cast h1
  · intro u hu
    funext τ
    have hw1 : hermC τ.1 X.Gm (u τ) (emb τ.1 ξ) = 0 := hu.1 τ
    have hw2 := huz u hu τ
    have hJw : hermC τ.1 X.Gm (X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 := by
      rw [X.Jp_adj hx]
      exact hw2
    have hIJw : hermC τ.1 X.Gm (I • X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 := by
      rw [hCsmul, hJw, mul_zero]
    have hπw : X.d2pi x τ (emb τ.1 ξ) (u τ) = u τ :=
      X.hyperbolic_projection_of_perp (x := x) (τ := τ) (e := emb τ.1 ξ) hx (hee τ) (hqne τ) hw1 hw2
    have hHfw : X.Hf (X.lmulC N x) τ (u τ) (emb τ.1 ξ) =
        -(δ τ (u τ) * X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) := by
      rw [hHfperp τ (u τ) hw1, hHfJ τ (u τ), hw2, hπw, zero_sub]
    have hHfIJw : X.Hf (X.lmulC N x) τ (I • X.Jp x τ (u τ)) (emb τ.1 ξ) =
        -(δ τ (X.d2pi x τ (emb τ.1 ξ) (I • X.Jp x τ (u τ))) *
          X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) := by
      rw [hHfperp τ _ hIJw, hHfJ τ, hCsmul, X.Jp_adj hx, X.Jp_Jp hx, hw1, mul_zero, zero_sub]
    have hcol : ∀ c, col (mat (X.lmulC N x) τ) c = (N τ).mulVec (col (mat x τ) c) := by
      intro c
      funext k
      simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rfl
    have hgramP : X.gramPos (X.lmulC N x) τ = X.gramPos x τ := by
      ext a b
      simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hcol, hU]
    have hJpN : ∀ v, X.Jp (X.lmulC N x) τ ((N τ).mulVec v) = (N τ).mulVec (X.Jp x τ v) := by
      intro v
      have hp : X.ppos (X.lmulC N x) τ ((N τ).mulVec v) = (N τ).mulVec (X.ppos x τ v) := by
        simp only [Data.ppos, hcol, hgramP, hU, Matrix.mulVec_sum, Matrix.mulVec_smul]
      simp only [Data.Jp, hp, Matrix.mulVec_sub, Matrix.mulVec_smul]
    have hNw : (N τ).mulVec (u τ) = u τ + δ τ (u τ) • emb τ.1 ξ :=
      X.unipotent_on_hyperbolic_complement (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hw1 hw2
    have hNJw : (N τ).mulVec (X.Jp x τ (u τ)) = X.Jp x τ (u τ) +
        δ τ (X.d2pi x τ (emb τ.1 ξ) (X.Jp x τ (u τ))) • emb τ.1 ξ :=
      X.unipotent_on_orthogonal_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hJw
    have hJz : X.Jz x u τ = I • X.Jp x τ (u τ) := rfl
    have hq0 := hqne τ
    show X.Jz x u τ - (X.Hf (X.lmulC N x) τ (X.Jz x u τ) (emb τ.1 ξ) /
        X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ =
      I • X.Jp (X.lmulC N x) τ (u τ - (X.Hf (X.lmulC N x) τ (u τ) (emb τ.1 ξ) /
        X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ)
    rw [hJz, hHfIJw, hHfw, hHfee τ, neg_div, neg_div, mul_div_assoc, div_self hq0, mul_one,
      mul_div_assoc, div_self hq0, mul_one, neg_smul, neg_smul, sub_neg_eq_add, sub_neg_eq_add,
      ← hNw, hJpN, hNJw, hπsmul, map_smul, smul_eq_mul, smul_add, smul_smul]
  · intro τ v
    exact X.unipotent_sub_one_majorant_bound (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ)
      (fun v => X.Hf_self hx τ v) (fun v hv => X.maj_pos hx τ hv) κ hκ0 hκ1
      (fun w hw1 hw2 => X.majorant_bound_orthogonal_part ξ x hx δ κ hδ τ w hw1 hw2) v

end Data

theorem unipotent_majorant_bound : ReducedFrameDomainCovering (E := E) := Data.unipotent_majorant_bound_data

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Metric Set

lemma exp_nine_quarters_lt : Real.exp (9 / 4) < 9.5 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 4, (1 / 4 : ℝ) ^ m / m.factorial| ≤
      |(1 / 4 : ℝ)| ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * 4)) :=
    Real.exp_bound (by norm_num [abs_of_pos]) (by norm_num)
  have h3 : Real.exp (1 / 4) < 1.2841 := by
    have := (abs_le.mp h2).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h4 : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he4 : 0 < Real.exp (1 / 4) := Real.exp_pos _
  rw [h4]
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) ≤ 2.7182818286 * 2.7182818286 * 1.2841 := by
        gcongr
    _ < 9.5 := by norm_num

theorem schwarzLemmaBall_holds : SchwarzLemmaBall := by
  intro V _ _ γ ρ S hρ hd hb h1 h2 Z hZ
  have hS : 0 < S := by linarith [norm_nonneg (γ 0)]
  have hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖γ z - γ 0‖ ≤ ‖γ z‖ + ‖γ 0‖ := norm_sub_le _ _
      _ ≤ Real.exp (9 / 4) * S + S := add_le_add (hb z (ball_subset_closedBall hz)) h2
      _ = (Real.exp (9 / 4) + 1) * S := by ring
  have hZρ : Z ∈ ball (0 : V) ρ := ball_subset_ball (by linarith) hZ
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ
  have hZn : ‖Z‖ < ρ / 21 := by simpa using hZ
  rw [dist_zero_right] at key
  intro h0
  rw [h0, dist_comm, dist_zero_right] at key
  have hexp := exp_nine_quarters_lt
  have : (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2 := by
    calc (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ ≤ (Real.exp (9 / 4) + 1) * S / ρ * (ρ / 21) := by
          gcongr
      _ = (Real.exp (9 / 4) + 1) * S / 21 := by field_simp
      _ < S / 2 := by nlinarith
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace IsotropicCoefficientLemmas

lemma smul_O {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  rfl

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (e : E) (x z : Fin r → E) :
    herm G (e • x) z = e * herm G x z := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def Mp {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin r → E) where
  carrier := {μ | μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0}
  add_mem' := fun ha hb => ⟨X.Λ.add_mem ha.1 hb.1, by rw [herm_add_left, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨X.Λ.zero_mem, by simp [herm]⟩
  smul_mem' := fun β μ h => ⟨X.Λ.smul_mem β h.1, by
    rw [smul_O, herm_smul_left, h.2, mul_zero]⟩

def Nx {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Mp X ξ) where
  carrier := {m | ∃ e : E, (m : Fin r → E) = e • ξ}
  add_mem' := by
    rintro m m' ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [Submodule.coe_add, he, he', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro β m ⟨e, he⟩
    exact ⟨(β : E) * e, by rw [Submodule.coe_smul, smul_O, he, smul_smul]⟩

lemma torsion_bot {r : ℕ} (X : Data E r) (ξ : Fin r → E) :
    Submodule.torsion (𝓞 E) (Mp X ξ ⧸ Nx X ξ) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨a, ha⟩, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have haq' : (a : 𝓞 E) • (Submodule.Quotient.mk m : Mp X ξ ⧸ Nx X ξ) = 0 := haq
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at haq'
  obtain ⟨e, he⟩ := haq'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have ha0 : (a : E) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero ha)
  rw [Submodule.coe_smul, smul_O] at he
  show ∃ e : E, (m : Fin r → E) = e • ξ
  refine ⟨e / a, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← he, smul_smul, inv_mul_cancel₀ ha0, one_smul]

end IsotropicCoefficientLemmas

open IsotropicCoefficientLemmas in
theorem isotropicCoefficientSplitting_holds : IsotropicCoefficientSplitting (E := E) := by
  intro r X ξ hξ
  classical
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have hle : Mp X ξ ≤ X.Λ := fun μ h => h.1
  haveI : Module.Finite (𝓞 E) (Mp X ξ) := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h1 : ((Mp X ξ).comap X.Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map X.Λ.subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Module.Finite.iff_fg.2 h2
  haveI : Module.Flat (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_bot X ξ)
  haveI : Module.FinitePresentation (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (Mp X ξ ⧸ Nx X ξ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Nx X ξ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  set ρ : Mp X ξ →ₗ[𝓞 E] Mp X ξ := LinearMap.id - s ∘ₗ (Nx X ξ).mkQ with hρdef
  have hρN : ∀ m, ∃ e : E, ((ρ m : Mp X ξ) : Fin r → E) = e • ξ := by
    intro m
    have h1 : (Nx X ξ).mkQ (s ((Nx X ξ).mkQ m)) = (Nx X ξ).mkQ m := LinearMap.congr_fun hs _
    have h2 : (Nx X ξ).mkQ (ρ m) = 0 := by
      rw [hρdef, LinearMap.sub_apply, map_sub, LinearMap.id_apply, LinearMap.comp_apply, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h2
  choose coef hcoef using hρN
  have hρid : ∀ m ∈ Nx X ξ, ρ m = m := by
    intro m hm
    have : (Nx X ξ).mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).2 hm
    simp [hρdef, this]
  have huniq : ∀ e e' : E, e • ξ = e' • ξ → e = e' := fun e e' h => smul_left_injective E hξ0 h
  have hmemMp : ∀ μ ∈ X.Λp ξ, μ ∈ Mp X ξ := fun μ h => ⟨h.1, h.2⟩
  refine ⟨fun μ => if h : μ ∈ Mp X ξ then coef ⟨μ, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    simp only [dif_pos (hmemMp μ hμ)]
    rw [← hcoef]
    exact (ρ _).2.1
  · intro μ hμ μ' hμ'
    have hs' := (Mp X ξ).add_mem (hmemMp μ hμ) (hmemMp μ' hμ')
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ), dif_pos (hmemMp μ' hμ')]
    apply huniq
    rw [← hcoef, add_smul, ← hcoef, ← hcoef]
    have : (⟨μ + μ', hs'⟩ : Mp X ξ) = ⟨μ, hmemMp μ hμ⟩ + ⟨μ', hmemMp μ' hμ'⟩ := rfl
    rw [this, map_add]
    rfl
  · intro α μ hμ
    have hs' : (α : E) • μ ∈ Mp X ξ := by
      rw [← smul_O]
      exact (Mp X ξ).smul_mem α (hmemMp μ hμ)
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ)]
    apply huniq
    rw [← hcoef, mul_smul, ← hcoef]
    have : (⟨(α : E) • μ, hs'⟩ : Mp X ξ) = α • ⟨μ, hmemMp μ hμ⟩ := Subtype.ext (smul_O α μ).symm
    rw [this, map_smul, Submodule.coe_smul, smul_O]
  · intro e he
    have hmem : e • ξ ∈ Mp X ξ := ⟨he, by rw [herm_smul_left, hξ.2.1, mul_zero]⟩
    simp only [dif_pos hmem]
    apply huniq
    rw [← hcoef, hρid _ ⟨e, rfl⟩]

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace RealTangentSpace

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def Usub (z : Frame X.Ψ r) (ξ : Fin r → E) : Submodule ℝ (X.Ψ → Fin r → ℂ) where
  carrier := X.Uz z ξ
  add_mem' := MajorantOperators.add_mem
  zero_mem' := MajorantOperators.zero_mem z ξ
  smul_mem' c u hu := by
    have h := MajorantOperators.smul_fam_mem (fun _ => (c : ℂ)) hu
    convert h using 1
    funext τ
    exact (Complex.coe_smul c (u τ)).symm

def VT (z : Frame X.Ψ r) (ξ : Fin r → E) : Type := ↥(Usub (X := X) z ξ)

variable (z : Frame X.Ψ r) (ξ : Fin r → E)

noncomputable instance : AddCommGroup (VT (X := X) z ξ) := inferInstanceAs (AddCommGroup ↥(Usub (X := X) z ξ))
noncomputable instance : Module ℝ (VT (X := X) z ξ) := inferInstanceAs (Module ℝ ↥(Usub (X := X) z ξ))
instance : FiniteDimensional ℝ (VT (X := X) z ξ) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(Usub (X := X) z ξ))

def VT.val {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : X.Ψ → Fin r → ℂ :=
  (u : ↥(Usub (X := X) z ξ)).1

theorem VT.val_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : u.val ∈ X.Uz z ξ := by
  exact (u : ↥(Usub (X := X) z ξ)).2

def VT.mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ) (hu : u ∈ X.Uz z ξ) :
    VT (X := X) z ξ := (⟨u, hu⟩ : ↥(Usub (X := X) z ξ))

@[simp] theorem VT.val_mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ)
    (hu : u ∈ X.Uz z ξ) : (VT.mk u hu).val = u := rfl

theorem VT.ext {z : Frame X.Ψ r} {ξ : Fin r → E} {u v : VT (X := X) z ξ} (h : u.val = v.val) :
    u = v := by
  exact Subtype.ext h

@[simp] theorem VT.val_add {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u + v).val = u.val + v.val := rfl

@[simp] theorem VT.val_smul {z : Frame X.Ψ r} {ξ : Fin r → E} (c : ℝ) (u : VT (X := X) z ξ) :
    (c • u).val = c • u.val := rfl

@[simp] theorem VT.val_zero {z : Frame X.Ψ r} {ξ : Fin r → E} : (0 : VT (X := X) z ξ).val = 0 := rfl

@[simp] theorem VT.val_neg {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) :
    (-u).val = -u.val := rfl

@[simp] theorem VT.val_sub {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u - v).val = u.val - v.val := rfl

variable [hz : Fact (z ∈ X.dom)]

@[instance_reducible]
noncomputable def core : InnerProductSpace.Core ℝ (VT (X := X) z ξ) where
  inner u v := MajorantOperators.gI z u.val v.val
  conj_inner_symm u v := by
    simp only [starRingEnd_apply, star_trivial]
    exact MajorantOperators.gI_comm hz.out _ _
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    rw [MajorantOperators.gI_self hz.out]
    exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _
  add_left u v w := by
    show MajorantOperators.gI z (u.val + v.val) w.val = _
    exact MajorantOperators.gI_add_left z _ _ _
  smul_left u v c := by
    show MajorantOperators.gI z (c • u.val) v.val = _
    rw [MajorantOperators.gI_smul_left]
    simp
  definite u h := by
    rw [MajorantOperators.gI_self hz.out] at h
    have h0 : ∀ τ ∈ Finset.univ, X.maj z τ (u.val τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _).mp h
    apply VT.ext
    funext τ
    by_contra hne
    exact (X.maj_pos hz.out τ hne).ne' (h0 τ (Finset.mem_univ τ))

noncomputable instance : NormedAddCommGroup (VT (X := X) z ξ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (VT (X := X) z ξ) _ _ _ (core z ξ)

noncomputable instance : InnerProductSpace ℝ (VT (X := X) z ξ) :=
  InnerProductSpace.ofCore (core z ξ).toCore

theorem inner_eq (u v : VT (X := X) z ξ) : inner ℝ u v = MajorantOperators.gI z u.val v.val := rfl

theorem norm_sq_eq (u : VT (X := X) z ξ) : ‖u‖ ^ 2 = ∑ τ, X.maj z τ (u.val τ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq, MajorantOperators.gI_self hz.out]

theorem maj_le_norm_sq (u : VT (X := X) z ξ) (τ : X.Ψ) : X.maj z τ (u.val τ) ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_eq]
  exact Finset.single_le_sum (fun σ _ => MajorantOperators.maj_nonneg hz.out σ _) (Finset.mem_univ τ)

omit hz in
theorem ucomp_add (u v : X.Ψ → Fin r → ℂ) :
    X.ucomp z ξ (u + v) = X.ucomp z ξ u + X.ucomp z ξ v := by
  have hHf : ∀ (σ : X.Ψ) (a b w : Fin r → ℂ),
      X.Hf z σ (a + b) w = X.Hf z σ a w + X.Hf z σ b w := by
    intro σ a b w
    rw [Data.Hf, Data.Hf, Data.Hf, Data.ppos_add, ← hermC_add_left]
    congr 1
    rw [smul_add]
    abel
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.add_apply, Pi.sub_apply, hHf, add_div, add_smul]
  abel

omit hz in
theorem ucomp_smul (a : ℝ) (u : X.Ψ → Fin r → ℂ) : X.ucomp z ξ (a • u) = a • X.ucomp z ξ u := by
  have hHf : ∀ (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ), X.Hf z σ (c • v) w = c * X.Hf z σ v w := by
    intro σ c v w
    have hp : X.ppos z σ (c • v) = c • X.ppos z σ v := by
      simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
    rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
    congr 1
    rw [smul_sub, smul_smul, smul_smul, mul_comm]
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.smul_apply, ← Complex.coe_smul,
    hHf]
  rw [smul_sub, mul_div_assoc, mul_smul]

theorem embV_add (u v : Fin r → E) : X.embV (u + v) = X.embV u + X.embV v := by
  funext τ a
  simp [Data.embV, Data.emb]

omit hz in
theorem embV_mem_Iperp {μ : Fin r → E} (hμ : μ ∈ X.Λp ξ) : X.embV μ ∈ X.Iperp ξ := by
  have hk : herm X.Gm μ ξ = 0 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2
  show ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.embV μ τ) (Data.emb τ.1 ξ) = 0
  intro τ
  simp only [Data.embV]
  rw [hermC_emb, hk, map_zero]

noncomputable def phi (hξ : X.IsIso ξ) : X.Λp ξ →+ VT (X := X) z ξ :=
  AddMonoidHom.mk' (fun μ => VT.mk (X.ucomp z ξ (X.embV μ))
      (orthogonal_lattice_decomposition r X ξ hξ z hz.out _ (embV_mem_Iperp ξ μ.2)))
    (fun μ ν => VT.ext (by
      simp only [VT.val_mk, VT.val_add, AddSubgroup.coe_add]
      rw [embV_add, ucomp_add]))

theorem phi_val (hξ : X.IsIso ξ) (μ : X.Λp ξ) : (phi z ξ hξ μ).val = X.ucomp z ξ (X.embV μ) := by
  rfl

noncomputable def Lat (hξ : X.IsIso ξ) : Submodule ℤ (VT (X := X) z ξ) :=
  (phi z ξ hξ).range.toIntSubmodule

theorem mem_Lat (hξ : X.IsIso ξ) {a : VT (X := X) z ξ} : a ∈ Lat z ξ hξ ↔ ∃ μ, phi z ξ hξ μ = a := by
  show a ∈ (phi z ξ hξ).range ↔ _
  exact AddMonoidHom.mem_range

private lemma Hf_smul_left_frame (y : Frame X.Ψ r) (σ : X.Ψ) (c : ℂ) (v w : Fin r → ℂ) :
    X.Hf y σ (c • v) w = c * X.Hf y σ v w := by
  have hp : X.ppos y σ (c • v) = c • X.ppos y σ v := by
    simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, mul_assoc, ← Finset.mul_sum]
  rw [Data.Hf, Data.Hf, hp, ← hermC_smul_left]
  congr 1
  rw [smul_sub, smul_smul, smul_smul, mul_comm]

theorem ucomp_line (hξ : X.IsIso ξ) (e : E) : X.ucomp z ξ (X.embV (e • ξ)) = 0 := by
  funext τ
  have hξ0 : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ.2.2
    funext a
    have := congrFun h a
    simpa [Data.emb] using this
  have hpos : X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hz.out]
    exact_mod_cast (X.maj_pos hz.out τ hξ0).ne'
  have hw : X.embV (e • ξ) τ = τ.1 e • Data.emb τ.1 ξ := by
    funext a
    simp [Data.embV, Data.emb]
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.sub_apply, Pi.zero_apply, hw, Hf_smul_left_frame,
    mul_div_assoc, div_self hpos, mul_one, sub_self]

theorem span_Lat (hD3 : IntegerApproximationCount (E := E)) (hξ : X.IsIso ξ) :
    Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let S : VT (X := X) z ξ →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun a => a.val
      map_add' := fun a b => VT.val_add a b
      map_smul' := fun c a => VT.val_smul c a }
  have hS : Function.Injective S := fun a b h => VT.ext h
  have h1 := LatticeSpanMembership.Uz_le_span hD3 hξ v.val_mem
  have h2 : Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) ≤
      Submodule.map S (Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := X) z ξ))) := by
    rw [Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    exact Submodule.mem_map_of_mem (Submodule.subset_span ((mem_Lat z ξ hξ).mpr ⟨μ, rfl⟩))
  obtain ⟨w, hw, hwv⟩ := h2 h1
  rwa [hS hwv] at hw

end RealTangentSpace

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscriminantTraceBounds

open NumberField Complex Module Matrix
open scoped ComplexConjugate nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

theorem norm_mul_discr_ge {x : E} (hx : x ≠ 0)
    (htr : ∀ β : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * β) = m) :
    1 ≤ |Algebra.norm ℚ x| * |(NumberField.discr E : ℚ)| := by
  classical
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top, Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h10
  have hmem : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨β, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := htr β
    refine ⟨m, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hm.symm
  have hsp : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ FractionalIdeal.dual ℤ ℚ 1 :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hdiff := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := by
    rw [hdiff]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
            first
            | exact mul_le_mul' hsp le_rfl
            | exact mul_right_mono hsp
            | exact FractionalIdeal.mul_right_mono _ hsp
      _ = 1 := mul_inv_cancel₀ hD0
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x *
      (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) ?_
    rw [hdiff]
    exact inv_ne_zero hD0
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0
    rw [← hI]
    simp
  have hnorm := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at hnorm
  have h1 : (1 : ℚ) ≤ (Ideal.absNorm I : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI0 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hnorm] at h1
  have h2 : (((NumberField.discr E).natAbs : ℕ) : ℚ) = |(NumberField.discr E : ℚ)| := by
    rw [Nat.cast_natAbs]
    push_cast
    rfl
  rw [h2] at h1
  exact h1

theorem abs_norm_eq_pow {x : E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ x‖ = a) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = a ^ finrank ℚ E := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = a ^ finrank ℚ E := by
    rw [h1, norm_prod, Finset.prod_congr rfl (fun σ _ => h σ.toRingHom), Finset.prod_const,
      Finset.card_univ, AlgHom.card]
  rw [← h2, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

section data

variable [IsCMField E] {r : ℕ} (X : DataX E r)

theorem exists_herm_ne (hr : 0 < r) : ∃ x ∈ X.L', ∃ y ∈ X.L', herm X.Gm x y ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hcc_add : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by
    unfold cc
    exact map_add _ a b
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  have hcc0 : cc (0 : E) = 0 := by
    unfold cc
    exact map_zero _
  have hcc1 : cc (1 : E) = 1 := by
    unfold cc
    exact map_one _
  have hadd2 : ∀ x y y' : Fin r → E, herm X.Gm x (y + y') = herm X.Gm x y + herm X.Gm x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, hcc_add, mul_add, Finset.sum_add_distrib]
  have hsmul2 : ∀ (x y : Fin r → E) (c : E), herm X.Gm x (c • y) = cc c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero2 : ∀ x : Fin r → E, herm X.Gm x 0 = 0 := fun x => by simp [herm, hcc0]
  have hadd1 : ∀ x x' y : Fin r → E, herm X.Gm (x + x') y = herm X.Gm x y + herm X.Gm x' y := by
    intro x x' y
    simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul1 : ∀ (x y : Fin r → E) (c : E), herm X.Gm (c • x) y = c * herm X.Gm x y := by
    intro x y c
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hzero1 : ∀ y : Fin r → E, herm X.Gm 0 y = 0 := fun y => by simp [herm]
  have hspan : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← X.Λ_span]
    apply Submodule.span_le.mpr
    intro z hz
    have h1 := X.NA_sub z hz
    have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
    have hz' : z = (X.NA : E)⁻¹ • ((X.NA : E) • z) := by
      rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hall2 : ∀ x ∈ X.L', ∀ y, herm X.Gm x y = 0 := by
    intro x hx y
    have hy : y ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact hcon x hx y hy
    | zero => exact hzero2 x
    | add y y' _ _ h1 h2 => rw [hadd2, h1, h2, add_zero]
    | smul c y _ h => rw [hsmul2, h, mul_zero]
  have hall : ∀ x y : Fin r → E, herm X.Gm x y = 0 := by
    intro x y
    have hx : x ∈ Submodule.span E (X.L' : Set (Fin r → E)) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact hall2 x hx y
    | zero => exact hzero1 y
    | add x x' _ _ h1 h2 => rw [hadd1, h1, h2, add_zero]
    | smul c x _ h => rw [hsmul1, h, mul_zero]
  have hG : X.Gm = 0 := by
    ext a b
    have hval : herm X.Gm (Pi.single a 1) (Pi.single b 1) = X.Gm a b := by
      simp [herm, Pi.single_apply, apply_ite cc, hcc1, hcc0]
    rw [Matrix.zero_apply, ← hval]
    exact hall _ _
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  exact X.Gm_det (by rw [hG]; exact Matrix.det_zero)

private theorem herm_smul_left_eq_mul (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem herm_smul_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G x (c • y) = cc c * herm G x y := by
  have hcc_mul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by
    unfold cc
    exact map_mul _ a b
  simp only [herm, Pi.smul_apply, smul_eq_mul, hcc_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem trace_int (hr : 0 < r) (c : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * c) = m := by
  classical
  set gens : Set (𝓞 E) := {c | ∃ x ∈ X.L', ∃ y ∈ X.L', (c : E) = herm X.Gm x y} with hgens
  set J : Ideal (𝓞 E) := Ideal.span gens with hJdef
  have hgen_mem : ∀ x ∈ X.L', ∀ y ∈ X.L', ∃ c ∈ J, (c : E) = herm X.Gm x y := by
    intro x hx y hy
    exact ⟨⟨herm X.Gm x y, X.L'_int x hx y hy⟩, Ideal.subset_span ⟨x, hx, y, hy, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨x, hx, y, hy, hne⟩ := exists_herm_ne X hr
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    intro hbot
    rw [hbot, Ideal.mem_bot] at hc
    apply hne
    rw [← hce, hc]
    simp
  have hJf0 : (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact hJ0
  have hmemJf : ∀ c ∈ J, ((c : 𝓞 E) : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) :=
    fun c hc => (FractionalIdeal.mem_coeIdeal _).mpr ⟨c, hc, rfl⟩
  have hinv : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ x ∈ X.L', t • x ∈ X.L' := by
    intro t ht x hx
    apply X.L'_dual
    intro y hy
    rw [herm_smul_left_eq_mul]
    obtain ⟨c, hc, hce⟩ := hgen_mem x hx y hy
    have h1 := (FractionalIdeal.mem_inv_iff hJf0).mp ht _ (hmemJf c hc)
    obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).mp h1
    rw [← hce, ← hd]
    exact RingOfIntegers.isIntegral_coe d
  have hmul : ∀ t ∈ (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹, ∀ c ∈ J,
      t * (c : E) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
    intro t ht c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      rw [hce, ← herm_smul_left_eq_mul]
      obtain ⟨c', hc', hce'⟩ := hgen_mem _ (hinv t ht x hx) y hy
      rw [← hce']
      exact hmemJf c' hc'
    | zero =>
      simp
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul a c _ h =>
      rw [smul_eq_mul]
      push_cast
      rw [mul_left_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a h
  have hle : (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * (J : FractionalIdeal (𝓞 E)⁰ E) ≤
      (J : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.mul_le.mpr fun t ht j hj => by
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    exact hmul t ht c hc
  rw [inv_mul_cancel₀ hJf0] at hle
  have hJtop : J = ⊤ := by
    rw [eq_top_iff]
    rw [← FractionalIdeal.coeIdeal_top] at hle
    exact (FractionalIdeal.coeIdeal_le_coeIdeal E).mp hle
  have hccNC : cc (X.NC : E) = X.NC := by
    unfold cc
    exact map_natCast _ _
  have hP : ∀ c ∈ J, ∀ a : 𝓞 E, ∃ m : ℤ,
      Algebra.trace ℚ E ((X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E))) = m := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      intro a
      obtain ⟨x, hx, y, hy, hce⟩ := hc
      have hax : (a : E) • x ∈ X.L' := by
        rw [show (a : E) • x = a • x from algebraMap_smul E a x]
        exact X.L'.smul_mem a hx
      obtain ⟨k, hk⟩ := X.EF_int _ (X.NC_sub _ hax) _ (X.NC_sub _ hy)
      refine ⟨-k, ?_⟩
      unfold EFf at hk
      rw [herm_smul_left_eq_mul, herm_smul_right_fundamental_domains, herm_smul_left_eq_mul, hccNC] at hk
      have h2 : (X.NC : E) ^ 2 * X.ξ0 * ((a : E) * (c : E)) =
          -(-X.ξ0 * ((X.NC : E) * ((X.NC : E) * ((a : E) * herm X.Gm x y)))) := by
        rw [hce]
        ring
      rw [h2, map_neg, hk]
      push_cast
      ring
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | add c c' _ _ h1 h2 =>
      intro a
      obtain ⟨m1, hm1⟩ := h1 a
      obtain ⟨m2, hm2⟩ := h2 a
      refine ⟨m1 + m2, ?_⟩
      push_cast
      rw [mul_add, mul_add, map_add, hm1, hm2]
    | smul b c _ h =>
      intro a
      obtain ⟨m, hm⟩ := h (a * b)
      refine ⟨m, ?_⟩
      rw [← hm, smul_eq_mul]
      push_cast
      ring_nf
  obtain ⟨m, hm⟩ := hP c (by rw [hJtop]; exact Submodule.mem_top) 1
  refine ⟨m, ?_⟩
  rw [← hm]
  simp

theorem two_le_normSq_mul_rootDisc (hr : 0 < r) : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
  set n := finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hNC : (0 : ℝ) < X.NC := Nat.cast_pos.mpr X.NC_pos
  have hx0 : ((X.NC : E) ^ 2 * X.ξ0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr X.NC_pos.ne')) X.ξ0_ne
  have h1 := norm_mul_discr_ge hx0 (fun β => by
    obtain ⟨m, hm⟩ := trace_int X hr β
    exact ⟨m, hm⟩)
  have habs : ∀ σ : E →+* ℂ, ‖σ ((X.NC : E) ^ 2 * X.ξ0)‖ = (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    intro σ
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
    congr 1
    by_cases hσ : σ ∈ X.Ψ
    · exact X.ξ0_abs ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        by_contra h'
        exact hσ ((X.cmType σ).mpr h')
      have h5 := X.ξ0_abs ⟨_, hc⟩
      simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h5
      exact h5
  have h2 := abs_norm_eq_pow habs
  have h3 : (1 : ℝ) ≤ |((Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0) : ℚ) : ℝ)| * dE E := by
    unfold dE
    have h1' : ((1 : ℚ) : ℝ) ≤
        ((|Algebra.norm ℚ ((X.NC : E) ^ 2 * X.ξ0)| * |(NumberField.discr E : ℚ)| : ℚ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact h1'
  rw [h2] at h3
  have ha : 0 < (X.NC : ℝ) ^ 2 * (X.k0 / 2) := by
    have := X.minWeight_pos
    positivity
  have hd : 0 ≤ dE E := abs_nonneg _
  have h4 : 1 ≤ (((X.NC : ℝ) ^ 2 * (X.k0 / 2)) ^ n * dE E) ^ (1 / (n : ℝ)) :=
    Real.one_le_rpow h3 (by positivity)
  rw [Real.mul_rpow (by positivity) hd, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
    mul_one_div_cancel (by positivity), Real.rpow_one] at h4
  unfold rdE
  rw [← hn_def]
  nlinarith [h4]

end data

end DiscriminantTraceBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscreteLatticeMinimum

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]

noncomputable def Bmap : VT (X := Y.toData) z ξ →ₗ[ℝ] VT (X := Y.toData) z ξ where
  toFun u := VT.mk (MajorantOperators.Bop z u.val) (MajorantOperators.Bop_mem hz.out u.val_mem)
  map_add' u v := VT.ext (by simp [MajorantOperators.Bop_add])
  map_smul' c u := VT.ext (by simp [MajorantOperators.Bop_smul])

theorem Bmap_val (u : VT (X := Y.toData) z ξ) : (Bmap z ξ u).val = MajorantOperators.Bop z u.val := rfl

theorem Bmap_Bmap (u : VT (X := Y.toData) z ξ) : Bmap z ξ (Bmap z ξ u) = (-(Y.k0 ^ 2)) • u := by
  apply VT.ext
  rw [Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]
  rfl

theorem inner_Bmap_right (u v : VT (X := Y.toData) z ξ) :
    inner ℝ u (Bmap z ξ v) = -inner ℝ (Bmap z ξ u) v := by
  rw [inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]

theorem norm_Bmap (u : VT (X := Y.toData) z ξ) : ‖Bmap z ξ u‖ = Y.k0 * ‖u‖ := by
  have h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq,
      Bmap_val, MajorantOperators.gI_Bop_self hz.out]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _))
    two_ne_zero).1 h

theorem Bmap_injective : Function.Injective (Bmap z ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := norm_Bmap z ξ u
  rw [hu, norm_zero] at h
  have h2 : ‖u‖ = 0 := by
    rcases mul_eq_zero.1 h.symm with h3 | h3
    · exact absurd h3 Y.minWeight_pos.ne'
    · exact h3
  exact norm_eq_zero.1 h2

noncomputable def Bequiv : VT (X := Y.toData) z ξ ≃ₗ[ℝ] VT (X := Y.toData) z ξ :=
  LinearEquiv.ofBijective (Bmap z ξ) ⟨Bmap_injective z ξ,
    LinearMap.surjective_of_injective (Bmap_injective z ξ)⟩

variable {ξ} (hξ : Y.IsIso ξ)

theorem mem_Lat_of_int (hD3 : IntegerApproximationCount (E := E)) (y : VT (X := Y.toData) z ξ)
    (hy : ∀ a ∈ Lat z ξ hξ, ∃ m : ℤ, inner ℝ y (Bmap z ξ a) = m) : y ∈ Lat z ξ hξ := by
  classical
  have hval : ∀ ν : Y.Λp ξ, inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) =
      (round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))) : ℝ) := by
    intro ν
    obtain ⟨m, hm⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
    rw [hm, round_intCast]
  let ψ : Y.Λp ξ →+ ℤ := AddMonoidHom.mk' (fun ν => round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))))
    (fun ν ν' => by
      obtain ⟨m1, hm1⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
      obtain ⟨m2, hm2⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν', rfl⟩)
      show round _ = round _ + round _
      rw [map_add, map_add, inner_add_right, hm1, hm2, ← Int.cast_add, round_intCast, round_intCast,
        round_intCast])
  have hψ : ∀ ν, (ψ ν : ℝ) = inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) := fun ν => (hval ν).symm
  have hvan : ∀ ν : Y.Λp ξ, (∃ e : E, (ν : Fin r → E) = e • ξ) → ψ ν = 0 := by
    rintro ν ⟨e, he⟩
    have h0 : phi z ξ hξ ν = 0 := VT.ext (by rw [phi_val, he, ucomp_line z ξ hξ e]; rfl)
    have := hψ ν
    rw [h0, map_zero, inner_zero_right] at this
    exact_mod_cast this
  obtain ⟨μ, hμ⟩ := (hermitian_dual_lattice_identity r Y ξ hξ).1 ψ hvan
  have hEF : ∀ ν : Y.Λp ξ,
      inner ℝ (Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) = 0 := by
    intro ν
    have h1 := hμ ν
    have h2 : ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) =
        inner ℝ (Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) := by
      rw [inner_eq, Bmap_val, phi_val, phi_val]
      exact MajorantOperators.EF_eq hz.out hξ.2.1 (LatticeSpanMembership.mem_Λp_iff.mp μ.2).2
        (LatticeSpanMembership.mem_Λp_iff.mp ν.2).2
    have h3 : (ψ ν : ℝ) = ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) := by exact_mod_cast h1
    rw [hψ, inner_Bmap_right, h2] at h3
    rw [inner_add_left]
    linarith
  set w := Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ) with hw
  have hwall : ∀ a ∈ Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := Y.toData) z ξ)),
      inner ℝ w a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨ν, rfl⟩ := (mem_Lat z ξ hξ).mp ha
      exact hEF ν
    | zero => exact inner_zero_right _
    | add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
    | smul c a _ iha => rw [inner_smul_right, iha, mul_zero]
  have hw0 : w = 0 := by
    have := hwall w (by rw [span_Lat z ξ hD3 hξ]; exact Submodule.mem_top)
    exact inner_self_eq_zero.mp this
  have hy0 : y + phi z ξ hξ μ = 0 := by
    apply Bmap_injective z ξ
    rw [map_add, ← hw, hw0, map_zero]
  have : y = phi z ξ hξ (-μ) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hy0
  rw [this]
  exact (mem_Lat z ξ hξ).mpr ⟨-μ, rfl⟩

section lattice

variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))

include hns in
theorem min_norm (a : VT (X := Y.toData) z ξ) (ha : a ∈ Lat z ξ hξ) (ha0 : a ≠ 0) :
    Real.sqrt ep0 / Y.NA ≤ ‖a‖ := by
  obtain ⟨μ, rfl⟩ := (mem_Lat z ξ hξ).mp ha
  have hμ := LatticeSpanMembership.mem_Λp_iff.mp μ.2
  have hNA : (Y.NA : E) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
  have hNAr : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
  obtain ⟨τ, hτ⟩ := hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1)
    (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero])
    (by
      intro e he
      apply ha0
      have hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ := by
        rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]
      exact VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))
  have hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ := by
    funext τ' b
    simp [Data.embV, Data.emb]
  rw [hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out] at hτ
  have h2 := maj_le_norm_sq z ξ (phi z ξ hξ μ) τ
  rw [phi_val] at h2
  have h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2 := by
    rw [mul_pow]
    exact le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  rw [div_le_iff₀ hNAr]
  linarith

include hns in
theorem discrete_Lat (hep : 0 < ep0) : DiscreteTopology (Lat z ξ hξ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hε : 0 < Real.sqrt ep0 / Y.NA :=
    div_pos (Real.sqrt_pos.mpr hep) (by exact_mod_cast Y.NA_pos)
  have hset : ({0} : Set (Lat z ξ hξ)) =
      Subtype.val ⁻¹' Metric.ball (0 : VT (X := Y.toData) z ξ) (Real.sqrt ep0 / Y.NA) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have := min_norm z hξ ep0 hns x.1 x.2 (fun h => hne (Subtype.ext h))
      linarith
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

include hns in
theorem short_basis (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) :
    ∃ y : Fin (finrank ℝ (VT (X := Y.toData) z ξ)) → VT (X := Y.toData) z ξ,
      LinearIndependent ℝ y ∧ (∀ i, y i ∈ Lat z ξ hξ) ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 /
        (Y.k0 * Real.sqrt ep0 / Y.NA) := by
  classical
  have := discrete_Lat z hξ ep0 hns hep
  have : IsZLattice ℝ (Lat z ξ hξ) := ⟨span_Lat z ξ hD3 hξ⟩
  have := ZLattice.module_free ℝ (Lat z ξ hξ)
  have := ZLattice.module_finite ℝ (Lat z ξ hξ)
  set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn
  let bZ := Module.Free.chooseBasis ℤ (Lat z ξ hξ)
  let bR := bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)
  have hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ := bZ.ofZLatticeBasis_span ℝ _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n :=
    (Module.finrank_eq_card_basis bR).symm
  let bF := bR.reindex (Fintype.equivFinOfCardEq hcard)
  have hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ := by
    rw [Basis.range_reindex]
    exact hspanR
  let e := (stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr
  let b' := (bF.map (Bequiv z ξ)).map e.toLinearEquiv
  have hb'j : ∀ j, b' j = e (Bmap z ξ (bF j)) := fun j => by
    simp only [b', Basis.map_apply]
    rfl
  set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam
  have hlam0 : 0 < lam := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  let f : VT (X := Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ
  have hfr : f '' Set.range bF = Set.range b' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hb'j j).symm)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    rw [← hfr, Submodule.span_image, hspanF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero f)
    have hfa : ‖f a‖ = Y.k0 * ‖a‖ := by
      show ‖e (Bmap z ξ a)‖ = _
      rw [LinearIsometryEquiv.norm_map, norm_Bmap]
    rw [hfa, hlam, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le
  obtain ⟨y, hli, hint, hnorm⟩ := T0.transference_dual b' lam hlam0 hmin
  refine ⟨fun i => e.symm (y i), ?_, ?_, ?_⟩
  · exact hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
  · intro i
    apply mem_Lat_of_int z hξ hD3
    intro a ha
    rw [← hspanF] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      obtain ⟨m, hm⟩ := hint i j
      refine ⟨m, ?_⟩
      rw [← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      exact ⟨m1 + m2, by rw [map_add, inner_add_right, h1, h2, Int.cast_add]⟩
    | smul c a _ iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨c * m, ?_⟩
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]
  · intro i
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm i

include hns in

theorem covering (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) (d : VT (X := Y.toData) z ξ) :
    ∃ μ : Y.Λp ξ, ‖d - phi z ξ hξ μ‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA /
      (2 * Y.k0 * Real.sqrt ep0) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos
  · have hsub : Subsingleton (VT (X := Y.toData) z ξ) := Module.finrank_zero_iff.mp h0
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]
    simp
  have : Nonempty (Fin (finrank ℝ (VT (X := Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨y, hli, hyL, hyn⟩ := short_basis z hξ ep0 hns hD3 hep
  let yb := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hyb : ∀ i, yb i = y i := fun i => Basis.mk_apply _ _ _
  set c := yb.repr d with hc
  set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp
  have hpL : p ∈ Lat z ξ hξ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)
  obtain ⟨μ, hμ⟩ := (mem_Lat z ξ hξ).mp hpL
  refine ⟨μ, ?_⟩
  rw [hμ]
  have hd : d = ∑ i, c i • y i := by
    conv_lhs => rw [← yb.sum_repr d]
    simp only [hyb, hc]
  have hdiff : d - p = ∑ i, (c i - round (c i)) • y i := by
    rw [hd, hp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [hdiff]
  have hlam0 : 0 < Y.k0 * Real.sqrt ep0 / Y.NA := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  calc ‖∑ i, (c i - round (c i)) • y i‖ ≤ ∑ i, ‖(c i - round (c i)) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ (VT (X := Y.toData) z ξ)), (1 / 2) *
        ((finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 / (Y.k0 * Real.sqrt ep0 / Y.NA)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)
    _ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 := Y.minWeight_pos.ne'
        have h2 : (Y.NA : ℝ) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
        have h3 := (Real.sqrt_pos.mpr hep).ne'
        field_simp

end lattice

end DiscreteLatticeMinimum

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FinrankRieszBounds

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring

variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]

theorem riesz (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add, Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith

omit hz in

theorem finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by
  classical
  let Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ) :=
    { toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ),
        hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)]
      map_add' := fun u v => by
        funext τ i
        fin_cases i <;> simp [hermC_add_left, Data.jp_add]
      map_smul' := fun c u => by
        funext τ i
        fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }
  have hker : LinearMap.ker Lm = Usub (X := X) z ξ := by
    ext u
    rw [LinearMap.mem_ker]
    show Lm u = 0 ↔ u ∈ X.Uz z ξ
    rw [MajorantOperators.mem_Uz_iff, funext_iff]
    refine forall_congr' fun τ => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp [Lm]
  have hsurj : LinearMap.range Lm = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    have hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0 := by
      intro τ
      rw [← Data.Hf_eq_jp, X.Hf_self hz]
      exact_mod_cast (X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'
    have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
      rw [hermC_emb, hξ.2.1, map_zero]
    refine ⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) •
        X.jp z τ (Data.emb τ.1 ξ) +
      (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩
    funext τ i
    fin_cases i
    · simp [Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]
    · simp [Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee,
        div_mul_cancel₀ _ (hm τ)]
  have hrn := LinearMap.finrank_range_add_finrank_ker Lm
  rw [hsurj, finrank_top, hker] at hrn
  have hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hdom, hcod] at hrn
  have hV : finrank ℝ (VT (X := X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl

  have hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E := by
    have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
      rw [Finset.disjoint_left]
      intro σ hσ hσ'
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ'
      exact (X.cmType τ).mp hτ hσ
    have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
      fun a b h => by
        have := congrArg ComplexEmbedding.conjugate h
        simpa using this
    have h1 := Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      NumberField.Embeddings.card] at h1
    rw [Fintype.card_coe]
    omega
  have hf : Fintype.card X.Ψ ≤ fdeg E := by
    unfold fdeg
    omega
  rw [hV]
  have hk : finrank ℝ (Usub (X := X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by
    rw [Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]
    ring_nf
  rw [hk]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)

end FinrankRieszBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module RealTangentSpace DiscreteLatticeMinimum
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem noShortVectorLowerBound_holds : NoShortVectorLowerBound (E := E) := by
  intro r X ξ ep0 hξ hep z hz hgap δ
  have hz' : z ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj z τ (Data.emb τ.1 ξ) = 1 := hz
  have hz1 : z ∈ X.dom := hz'.1
  haveI hzf : Fact (z ∈ X.dom) := ⟨hz1⟩
  have hk0 : 0 < X.k0 := X.minWeight_pos
  have hk0ne : X.k0 ≠ 0 := hk0.ne'
  have hdE : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero (K := E)))
  have hdEne : dE E ≠ 0 := hdE.ne'
  have hrd : 0 ≤ rdE E := by
    unfold rdE
    exact Real.rpow_nonneg hdE.le _
  have hepne : ep0 ≠ 0 := hep.ne'
  obtain ⟨d, hd⟩ : ∃ d : VT (X := X.toData) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
    apply FinrankRieszBounds.riesz <;> assumption
  obtain ⟨d', hd'⟩ : ∃ d' : VT (X := X.toData) z ξ,
      d' = (2 / (dE E * X.k0 ^ 2)) • Bmap z ξ d := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : X.Λp ξ, ‖d' - phi z ξ hξ μ‖ ≤
      (finrank ℝ (VT (X := X.toData) z ξ) : ℝ) ^ 3 * X.NA / (2 * X.k0 * Real.sqrt ep0) := by
    apply DiscreteLatticeMinimum.covering (Y := X) (z := z) (ξ := ξ) (hD3 := integerApproximationCount_holds) (hep := hep) <;> assumption
  have hfin : finrank ℝ (VT (X := X.toData) z ξ) ≤ 2 * fdeg E * (r - 2) := by
    apply FinrankRieszBounds.finrank_le <;> assumption
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = finrank ℝ (VT (X := X.toData) z ξ) := ⟨_, rfl⟩
  rw [← hn] at hμ hfin
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ‖d' - phi z ξ hξ μ‖ := ⟨_, rfl⟩
  rw [← hDdef] at hμ
  obtain ⟨w, hw⟩ : ∃ w : VT (X := X.toData) z ξ,
      w = (-(dE E / 2)) • Bmap z ξ (d' - phi z ξ hξ μ) := ⟨_, rfl⟩
  have hd_eq : (-(dE E / 2)) • Bmap z ξ d' = d := by
    rw [hd', map_smul, DiscreteLatticeMinimum.Bmap_Bmap, smul_smul, smul_smul]
    convert one_smul ℝ d using 2
    field_simp <;> ring
  have hw_eq : w = d - (-(dE E / 2)) • Bmap z ξ (phi z ξ hξ μ) := by
    rw [hw, map_sub, smul_sub, hd_eq]
  have hwn : ‖w‖ = dE E / 2 * (X.k0 * D) := by
    rw [hw, norm_smul, DiscreteLatticeMinimum.norm_Bmap, ← hDdef, Real.norm_eq_abs, abs_neg,
      abs_of_pos (half_pos hdE)]
  have hspos : 0 < Real.sqrt ep0 := Real.sqrt_pos.mpr hep
  have hsq : Real.sqrt ep0 ^ 2 = ep0 := Real.sq_sqrt hep.le
  have hden : 0 < 2 * X.k0 * Real.sqrt ep0 := mul_pos (mul_pos two_pos hk0) hspos
  have hD0 : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
  have hB : D * (2 * X.k0 * Real.sqrt ep0) ≤ (n : ℝ) ^ 3 * X.NA := (le_div_iff₀ hden).mp hμ
  have hD2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) ≤ ((n : ℝ) ^ 3 * X.NA) ^ 2 := by
    have h0 : 0 ≤ D * (2 * X.k0 * Real.sqrt ep0) := mul_nonneg hD0 hden.le
    have h1 := pow_le_pow_left₀ h0 hB 2
    have h2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) = (D * (2 * X.k0 * Real.sqrt ep0)) ^ 2 := by
      linear_combination (-(4 * D ^ 2 * X.k0 ^ 2)) * hsq
    rw [h2]
    exact h1
  have hx : 0 ≤ (X.NC : ℝ) ^ 2 * rdE E / ep0 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hrd) hep.le
  have hM2 : frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 =
      (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 * (X.NA : ℝ) ^ 2 *
        ((X.NC : ℝ) ^ 2 * rdE E / ep0) := by
    have hs := Real.sq_sqrt hx
    rw [frameIndexBound]
    linear_combination ((fdeg E : ℝ) * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 3 * dE E *
      (X.NA : ℝ)) ^ 2 * hs
  have hwM : ‖w‖ ^ 2 ≤ frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0 := by
    rw [hwn, hM2]
    have hlhs : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by
      have h3 : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) =
          dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) := by ring
      rw [h3]
      calc dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) ≤ dE E ^ 2 * (((n : ℝ) ^ 3 * X.NA) ^ 2) :=
            mul_le_mul_of_nonneg_left hD2 (sq_nonneg _)
        _ = dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by ring
    have hQ : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    have hS : 0 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hk0.le) hrd
    have hn6 : (n : ℝ) ^ 6 ≤ ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfin) 6
    have hinv : ep0 * ep0⁻¹ = 1 := mul_inv_cancel₀ hepne
    have heq : (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 *
        (X.NA : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * rdE E / ep0) * X.k0 * (16 * ep0) =
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      linear_combination (16 * (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 *
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (X.NC : ℝ) ^ 2 * rdE E * X.k0) * hinv
    have hP : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 := by
      positivity
    have h6 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hn6 hQ
    have hrhs : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      by_cases hN : ((2 * fdeg E * (r - 2) : ℕ) : ℝ) = 0
      · have hP0 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 = 0 := by
          rw [hN]; ring
        have h5 : 0 ≤ 16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
            ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) :=
          mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hP)) hS
        linarith
      · have hN' : 2 * fdeg E * (r - 2) ≠ 0 := by exact_mod_cast hN
        have hf0 : fdeg E ≠ 0 := fun h => hN' (by simp [h])
        have hr : 0 < r := Nat.pos_of_ne_zero (fun h => hN' (by simp [h]))
        have hk : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
          apply DiscriminantTraceBounds.two_le_normSq_mul_rootDisc <;> assumption
        have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ 2 := by
          have h1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf0
          nlinarith
        have h7 : 2 ≤ (fdeg E : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by nlinarith
        have h8 := mul_le_mul_of_nonneg_left h7 hP
        linarith
    exact le_of_mul_le_mul_right (hlhs.trans (hrhs.trans_eq heq.symm)) (mul_pos (by norm_num) hep)
  refine ⟨(μ : Fin r → E), μ.2, ?_⟩
  intro u hu τ
  have hsm : ∀ (c : ℝ) (v : Fin r → ℂ),
      X.Hf z τ (u τ) (c • v) = (c : ℂ) * X.Hf z τ (u τ) v := by
    intro c v
    have hcv : c • v = (c : ℂ) • v := (Complex.coe_smul c v).symm
    rw [hcv, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal]
  have hkey : δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
      hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV (μ : Fin r → E)) τ) =
      X.Hf z τ (u τ) (w.val τ) := by
    rw [hw_eq, VT.val_sub, VT.val_smul, Pi.sub_apply, Pi.smul_apply, MajorantOperators.Hf_sub_right,
      ← hd u hu τ, DiscreteLatticeMinimum.Bmap_val, RealTangentSpace.phi_val]
    congr 1
    rw [hsm]
    simp only [MajorantOperators.Bop]
    rw [UnipotentCoefficientShift.Hf_smul_right, Data.Hf_eq_jp, X.hermC_jp_jp hz1]
    simp only [map_mul, map_neg, map_ofNat, MajorantOperators.conj_purely_imaginary_generator]
    push_cast
    ring
  rw [hkey, FinrankRieszBounds.maj_csmul hz1]
  have hc : X.k0 * X.maj z τ (Data.emb τ.1 ξ) = 1 := by
    have h2 := hz'.2 τ
    simp only [Data.c] at h2
    rw [X.ξ0_abs τ] at h2
    linear_combination h2
  have hme : 0 ≤ X.maj z τ (Data.emb τ.1 ξ) := MajorantOperators.maj_nonneg hz1 τ _
  have hmu : 0 ≤ X.maj z τ (u τ) := MajorantOperators.maj_nonneg hz1 τ _
  have hcs := MajorantOperators.Hf_cs hz1 τ (u τ) (w.val τ)
  have hmw : X.maj z τ (w.val τ) ≤ ‖w‖ ^ 2 := by
    apply RealTangentSpace.maj_le_norm_sq
  calc ‖X.Hf z τ (u τ) (w.val τ)‖ ^ 2 * X.maj z τ (Data.emb τ.1 ξ)
      ≤ (X.maj z τ (u τ) * X.maj z τ (w.val τ)) * X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right hcs hme
    _ ≤ (X.maj z τ (u τ) * (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0)) *
        X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmw.trans hwM) hmu) hme
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) *
        (X.k0 * X.maj z τ (Data.emb τ.1 ξ)) := by ring
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) := by
        rw [hc, mul_one]

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]




end ReciprocityTheory.ChartRestriction.G.FD
end
