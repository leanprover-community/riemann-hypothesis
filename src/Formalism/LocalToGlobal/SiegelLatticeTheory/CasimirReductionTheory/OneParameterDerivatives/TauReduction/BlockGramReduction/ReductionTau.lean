import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.ReductionTauOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfFinitelyGenerated
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.PacketConditionsClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Module.ZLattice.Covolume

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem inclE_mem_intAf (I : AutInst) (c : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  left
  exact ⟨⟨(c : I.E), c, rfl⟩, rfl⟩

def latSubmodule (I : AutInst) (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := latSet I x
  zero_mem' := by
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have : (fun i : Fin I.n => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
      funext i; simp
    rw [this, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  add_mem' := by
    intro u w hu hw
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + w) i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
      funext i; simp
    rw [h, Matrix.mulVec_add]
    exact I.Lf.add_mem hu hw
  smul_mem' := by
    intro c u hu
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((c • u) i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) •
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) := by
      funext i
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul]
    have := I.Lf.smul_mem (⟨_, inclE_mem_intAf I c⟩ : IntAf I.F I.E) hu
    exact this

theorem coe_latSubmodule (I : AutInst) (x : I.GA) :
    ((latSubmodule I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = latSet I x := rfl

theorem lattice_finitelyGenerated_of_commensurable (h0 : LatticeCommensurable) : LatticeFinitelyGenerated := by
  intro I x
  obtain ⟨m, hm1, hA, -⟩ := h0 I x
  refine ⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    (((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
  have hle : latSubmodule I x ≤ I.L.map φ := by
    intro u hu
    refine ⟨(m : I.E) • u, hA u hu, ?_⟩
    simp [φ, smul_smul, inv_mul_cancel₀ hm0]
  have hfg : (I.L.map φ).FG := I.L_fg.map φ
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  have h1 := IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)
  have h2 := h1.map (I.L.map φ).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem kset_inv_mem (I : AutInst) {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hk

theorem t4 : LatticeRightInvariant := by
  intro I x y k hk
  ext u
  show (I.fmat (x * (y, k)).2⁻¹) *ᵥ _ ∈ I.Lf ↔ (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
  have hk' : ∀ w, w ∈ I.Lf ↔ I.fmat k⁻¹ *ᵥ w ∈ I.Lf := kset_inv_mem I hk
  have e : I.fmat (x * (y, k)).2⁻¹ = I.fmat k⁻¹ * I.fmat x.2⁻¹ := by
    simp only [AutInst.fmat, Prod.snd_mul, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul]
  rw [e, ← Matrix.mulVec_mulVec]
  exact (hk' _).symm

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open Matrix

open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

theorem re_star_dotProduct_self {m : ℕ} (z : Fin m → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem star_dotProduct_gram {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ) (z : Fin k → ℂ) :
    star z ⬝ᵥ ((Aᴴ * A) *ᵥ z) = star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem det_bounds_of_rayleigh {j : ℕ} (M : Matrix (Fin j) (Fin j) ℂ) (hM : M.IsHermitian) (a b : ℝ)
    (ha : 0 ≤ a)
    (h : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2) :
    ∃ μ : ℝ, M.det = μ ∧ a ^ j ≤ μ ∧ μ ≤ b ^ j := by
  have key : ∀ i, a ≤ hM.eigenvalues i ∧ hM.eigenvalues i ≤ b := by
    intro i
    set v : Fin j → ℂ := (hM.eigenvectorBasis i).ofLp with hv_def
    have hnorm : ∑ k, ‖v k‖ ^ 2 = 1 := by
      have h1 := (hM.eigenvectorBasis).norm_eq_one i
      rw [EuclideanSpace.norm_eq] at h1
      have h2 := congrArg (fun t : ℝ => t ^ 2) h1
      simp only [one_pow] at h2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    have e : (star v ⬝ᵥ (M *ᵥ v)).re = hM.eigenvalues i := by
      rw [hv_def, hM.mulVec_eigenvectorBasis i, dotProduct_smul, Complex.smul_re, smul_eq_mul,
        ← hv_def, re_star_dotProduct_self, hnorm, mul_one]
    have := h v
    rw [e, hnorm, mul_one, mul_one] at this
    exact this
  refine ⟨∏ i, hM.eigenvalues i, ?_, ?_, ?_⟩
  · rw [hM.det_eq_prod_eigenvalues]
    norm_cast
  · calc a ^ j = ∏ _i : Fin j, a := by simp
      _ ≤ ∏ i, hM.eigenvalues i := Finset.prod_le_prod (fun _ _ => ha) (fun i _ => (key i).1)
  · calc ∏ i, hM.eigenvalues i ≤ ∏ _i : Fin j, b :=
          Finset.prod_le_prod (fun i _ => ha.trans (key i).1) (fun i _ => (key i).2)
      _ = b ^ j := by simp

theorem exists_mul_mul_conjTranspose_eq_one {j : ℕ} {G : Matrix (Fin j) (Fin j) ℂ} (hG : G.PosDef) :
    ∃ S : Matrix (Fin j) (Fin j) ℂ, S * G * Sᴴ = 1 := by
  have hH := hG.isHermitian
  set U : Matrix (Fin j) (Fin j) ℂ := (hH.eigenvectorUnitary : Matrix (Fin j) (Fin j) ℂ) with hU_def
  have hU : star U * U = 1 := by simp [U]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hG.eigenvalues_pos
  refine ⟨diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U, ?_⟩
  rw [show (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) * G *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ =
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U) *
      (U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U) *
      (diagonal (fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ)) * star U)ᴴ by rw [← hspec]]
  rw [conjTranspose_mul, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
    ← Matrix.star_eq_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hU, Matrix.one_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  have hs : 0 < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
  have hsq : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt (hpos i).le
  have h1 : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    rw [show (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹
        = hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i) ^ 2)⁻¹ by ring, hsq, mul_inv_cancel₀ (hpos i).ne']
  simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  push_cast at h2
  simpa using h2

theorem det_gram_mul_eq_zero {n j : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin n) (Fin j) ℂ)
    (hd : (Cᴴ * C).det = 0) : ((Y * C)ᴴ * (Y * C)).det = 0 := by
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hCz : C *ᵥ z = 0 := by
    have h1 : star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = 0 := by rw [hz, dotProduct_zero]
    rw [star_dotProduct_gram] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨z, hz0, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCz, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem t5 : GramDistortionBound := by
  intro n j Y C a b ha hY
  by_cases hd : (Cᴴ * C).det = 0
  · rw [hd, det_gram_mul_eq_zero Y C hd]
    simp
  have hPS : (Cᴴ * C).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hPD : (Cᴴ * C).PosDef := hPS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨S, hS⟩ := exists_mul_mul_conjTranspose_eq_one hPD
  set V := C * Sᴴ with hV_def
  have hV : Vᴴ * V = 1 := by
    rw [hV_def, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [show S * Cᴴ * (C * Sᴴ) = S * (Cᴴ * C) * Sᴴ by simp only [Matrix.mul_assoc]]
    exact hS
  set M := (Y * V)ᴴ * (Y * V) with hM_def
  have hMH : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hray : ∀ z : Fin j → ℂ, a * ∑ i, ‖z i‖ ^ 2 ≤ (star z ⬝ᵥ (M *ᵥ z)).re ∧
      (star z ⬝ᵥ (M *ᵥ z)).re ≤ b * ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have e1 : (star z ⬝ᵥ (M *ᵥ z)).re = ∑ i, ‖((Y * V) *ᵥ z) i‖ ^ 2 := by
      rw [hM_def, star_dotProduct_gram, re_star_dotProduct_self]
    have e2 : ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
      rw [← re_star_dotProduct_self, ← star_dotProduct_gram, hV, Matrix.one_mulVec, re_star_dotProduct_self]
    have := hY (V *ᵥ z)
    rw [Matrix.mulVec_mulVec, e2] at this
    rw [e1]
    exact this
  obtain ⟨μ, hμ, h1, h2⟩ := det_bounds_of_rayleigh M hMH a b ha hray
  have hMeq : M = S * ((Y * C)ᴴ * (Y * C)) * Sᴴ := by
    simp only [hM_def, hV_def, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hdet1 : S.det * (Cᴴ * C).det * Sᴴ.det = 1 := by
    rw [← det_mul, ← det_mul, hS, det_one]
  have hdY : ((Y * C)ᴴ * (Y * C)).det = μ * (Cᴴ * C).det := by
    calc ((Y * C)ᴴ * (Y * C)).det
        = ((Y * C)ᴴ * (Y * C)).det * (S.det * (Cᴴ * C).det * Sᴴ.det) := by rw [hdet1, mul_one]
      _ = (S.det * ((Y * C)ᴴ * (Y * C)).det * Sᴴ.det) * (Cᴴ * C).det := by ring
      _ = μ * (Cᴴ * C).det := by rw [← det_mul, ← det_mul, ← hMeq, hμ]
  have hG0 := hPS.det_nonneg
  rw [Complex.nonneg_iff] at hG0
  have hre : ((Y * C)ᴴ * (Y * C)).det.re = μ * (Cᴴ * C).det.re := by
    rw [hdY, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  exact ⟨mul_le_mul_of_nonneg_right h1 hG0.1, mul_le_mul_of_nonneg_right h2 hG0.1⟩

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem norm_add_sq_le_young (p q : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖p + q‖ ^ 2 ≤ (1 + t) * ‖p‖ ^ 2 + (1 + 1 / t) * ‖q‖ ^ 2 := by
  have ha := norm_nonneg p
  have hb := norm_nonneg q
  have h1 : ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q
  have h2 : ‖p + q‖ ^ 2 ≤ (‖p‖ + ‖q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖p‖ * ‖q‖ ≤ t * ‖p‖ ^ 2 + 1 / t * ‖q‖ ^ 2 := by
    have h4 : 0 ≤ (t * ‖p‖ - ‖q‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖p‖ - ‖q‖) ^ 2 / t = t * ‖p‖ ^ 2 - 2 * ‖p‖ * ‖q‖ + 1 / t * ‖q‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

theorem norm_sum_mul_sq_le {m : ℕ} (d w : Fin m → ℂ) :
    ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2 := by
  have h1 : ‖∑ l, d l * w l‖ ≤ ∑ l, ‖d l‖ * ‖w l‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖d l‖) (fun l => ‖w l‖)
  calc ‖∑ l, d l * w l‖ ^ 2 ≤ (∑ l, ‖d l‖ * ‖w l‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem sum_norm_mulVec_sq_le {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (w : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      ((1 + t) + (1 + 1 / t) * ∑ i, ∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
  have hY : ∀ i, (Y *ᵥ w) i = w i + ((Y - 1) *ᵥ w) i := by
    intro i
    simp [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hc : 0 ≤ 1 + 1 / t := by
    have := one_div_pos.mpr ht
    linarith
  have hi : ∀ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤
      (1 + t) * ‖w i‖ ^ 2 + (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2) := by
    intro i
    rw [hY]
    refine (norm_add_sq_le_young _ _ ht).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le _ _) hc)
  calc ∑ i, ‖(Y *ᵥ w) i‖ ^ 2 ≤ ∑ i, ((1 + t) * ‖w i‖ ^ 2 +
        (1 + 1 / t) * ((∑ l, ‖(Y - 1) i l‖ ^ 2) * ∑ l, ‖w l‖ ^ 2)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

variable (I : AutInst)

def cmat (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  Matrix.of fun i a => coordV I x v (b a) i

theorem gramV_eq (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (cmat I x v b)ᴴ * cmat I x v b := by
  ext a c
  simp [gramV, cmat, Matrix.mul_apply, Matrix.conjTranspose_apply]

def subOfEq {x x' : I.GA} (h : latSet I x' = latSet I x) (s : Sub I x) : Sub I x' where
  j := s.j
  j_pos := s.j_pos
  b := s.b
  b_ind := s.b_ind
  B := s.B
  B_lat := by rw [h]; exact s.B_lat
  b_mem := s.b_mem
  B_span := s.B_span

theorem det_gram_nonneg (h5 : GramDistortionBound) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (hj : 1 ≤ j)
    (b : Fin j → Fin I.n → I.E) : 0 ≤ (gramV I x v b).det.re := by
  rw [gramV_eq]
  open scoped ComplexOrder in
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1

theorem ht_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ ht I s := by
  unfold ht
  exact div_nonneg (Finset.prod_nonneg fun v _ => det_gram_nonneg I h5 x v s.j_pos s.b) (Nat.cast_nonneg _)

theorem size_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ size I s := by
  unfold Size.size
  exact Real.rpow_nonneg (ht_nonneg I h5 s) _

theorem size_subOfEq_le (h5 : GramDistortionBound) {x x' : I.GA} (hlat : latSet I x' = latSet I x)
    (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (hY : ∀ v u, coordV I x' v u = Y v *ᵥ coordV I x v u) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(Y v *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2) (s : Sub I x) :
    size I (subOfEq I hlat s) ≤ c ^ Fintype.card (InfinitePlace I.F) * size I s := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcm : ∀ v, cmat I x' v s.b = Y v * cmat I x v s.b := by
    intro v
    ext i a
    simp [cmat, hY, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hdet : ∀ v, (gramV I x' v s.b).det.re ≤ c ^ s.j * (gramV I x v s.b).det.re := by
    intro v
    rw [gramV_eq, gramV_eq, hcm]
    refine (h5 I.n s.j (Y v) (cmat I x v s.b) 0 c le_rfl (fun w => ⟨?_, hb v w⟩)).2
    rw [zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hht : ht I (subOfEq I hlat s) ≤ (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s := by
    unfold ht
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc ∏ v, (gramV I x' v (subOfEq I hlat s).b).det.re
        ≤ ∏ v : InfinitePlace I.F, c ^ s.j * (gramV I x v s.b).det.re :=
          Finset.prod_le_prod (fun v _ => det_gram_nonneg I h5 x' v s.j_pos s.b) (fun v _ => hdet v)
      _ = (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ∏ v, (gramV I x v s.b).det.re := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have he : 0 ≤ 1 / (2 * (I.f : ℝ) * (s.j : ℝ)) := by positivity
  have hexp : ((s.j * Fintype.card (InfinitePlace I.F) : ℕ) : ℝ) * (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ (Fintype.card (InfinitePlace I.F) : ℝ) := by
    have hj : (1 : ℝ) ≤ s.j := by exact_mod_cast s.j_pos
    rcases Nat.eq_zero_or_pos I.f with hf | hf
    · simp [hf]
    · have hf' : (1 : ℝ) ≤ I.f := by exact_mod_cast hf
      rw [Nat.cast_mul, mul_one_div, div_le_iff₀ (by positivity)]
      have hP : (0 : ℝ) ≤ Fintype.card (InfinitePlace I.F) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hP (by linarith : (0 : ℝ) ≤ s.j)) (by linarith : (0 : ℝ) ≤ 2 * (I.f : ℝ) - 1)]
  unfold Size.size
  show ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) ≤ _
  calc ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.rpow_le_rpow (ht_nonneg I h5 _) hht he
    _ = ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F)) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) *
          ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.mul_rpow (by positivity) (ht_nonneg I h5 s)
    _ ≤ c ^ Fintype.card (InfinitePlace I.F) * ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ht_nonneg I h5 s) _)
        rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hc0, ← Real.rpow_natCast c]
        exact Real.rpow_le_rpow_of_exponent_le hc hexp

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem uMat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := by
  simp [uMat]

theorem uMat_one {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := by
  simp [uMat]

theorem coordV_mul (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I (x * (y, k)) v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
  have hA : ((x * (y, k)).1 v)⁻¹ = (y v)⁻¹ * (x.1 v)⁻¹ := by
    rw [← _root_.mul_inv_rev]
    rfl
  unfold coordV
  rw [hA, uMat_mul, Matrix.mulVec_mulVec, mul_assoc]

theorem coordV_mul' (I : AutInst) (x : I.GA) (y : I.Ginf) (k : I.Gf) (v : InfinitePlace I.F)
    (u : Fin I.n → I.E) : coordV I x v u = uMat (y v) *ᵥ coordV I (x * (y, k)) v u := by
  rw [coordV_mul, Matrix.mulVec_mulVec, ← uMat_mul, mul_inv_cancel, uMat_one, Matrix.one_mulVec]

theorem eventually_uMat_near (I : AutInst) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 (1 : I.Ginf), ∀ v, ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 < δ := by
  rw [Filter.eventually_all]
  intro v
  have c1 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v)⁻¹ - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  have c2 : Continuous fun y : I.Ginf => ∑ i, ∑ l, ‖(uMat (y v) - 1) i l‖ ^ 2 := by
    unfold uMat
    fun_prop
  refine Filter.Eventually.and ?_ ?_
  · exact c1.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)
  · exact c2.continuousAt.eventually_lt continuousAt_const (by simpa [uMat_one] using hδ)

theorem eventually_kg_one (I : AutInst) : ∀ᶠ k in 𝓝 (1 : I.Gf), k ∈ I.Kg 1 := by
  have ho := I.topf_open 1 le_rfl
  refine ho.mem_nhds ?_
  exact ⟨Subgroup.one_mem _, fun y _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩

theorem sizes_locally_comparable (h4 : LatticeRightInvariant) (h5 : GramDistortionBound) : SizesLocallyComparable := by
  intro I x r hr
  set N := Fintype.card (InfinitePlace I.F)
  set c : ℝ := r ^ (((N + 1 : ℕ) : ℝ)⁻¹) with hcdef
  have hc1 : 1 < c := Real.one_lt_rpow hr (by positivity)
  have hcN : c ^ N ≤ r := by
    calc c ^ N ≤ c ^ (N + 1) := pow_le_pow_right₀ hc1.le (Nat.le_succ N)
      _ = r := Real.rpow_inv_natCast_pow (by linarith) (Nat.succ_ne_zero N)
  set ε : ℝ := (c - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set δ : ℝ := ε ^ 2 / (1 + ε) with hδdef
  have hδ : 0 < δ := by positivity
  have hbound : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 < δ →
      ∀ w : Fin I.n → ℂ, ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2 := by
    intro M hM w
    refine (sum_norm_mulVec_sq_le M w hε).trans ?_
    have hw : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hw
    have h1 : (1 + 1 / ε) * ∑ i, ∑ l, ‖(M - 1) i l‖ ^ 2 ≤ (1 + 1 / ε) * δ :=
      mul_le_mul_of_nonneg_left hM.le (by positivity)
    have h2 : (1 + 1 / ε) * δ = ε := by
      rw [hδdef]
      field_simp
      ring
    linarith
  have hW : ∀ᶠ z in 𝓝 (1 : I.GA), (∀ v, ∑ i, ∑ l, ‖(uMat (z.1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat (z.1 v) - 1) i l‖ ^ 2 < δ) ∧ z.2 ∈ I.Kg 1 := by
    have h := (eventually_uMat_near I hδ).prod_mk (eventually_kg_one I)
    rw [show (1 : I.GA) = (1, 1) from rfl, nhds_prod_eq]
    exact h
  have hx : ∀ᶠ x' in 𝓝 x, (∀ v, ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v)⁻¹ - 1) i l‖ ^ 2 < δ ∧
      ∑ i, ∑ l, ‖(uMat ((x⁻¹ * x').1 v) - 1) i l‖ ^ 2 < δ) ∧ (x⁻¹ * x').2 ∈ I.Kg 1 := by
    have ht : Tendsto (fun x' : I.GA => x⁻¹ * x') (𝓝 x) (𝓝 1) := by
      have h := (continuous_const_mul x⁻¹).tendsto x
      rwa [inv_mul_cancel] at h
    exact ht.eventually hW
  filter_upwards [hx] with x' hx'
  obtain ⟨hy, hk⟩ := hx'
  set y := (x⁻¹ * x').1
  set k := (x⁻¹ * x').2
  have hxe : x * (y, k) = x' := by
    change x * ((x⁻¹ * x').1, (x⁻¹ * x').2) = x'
    rw [Prod.mk.eta, mul_inv_cancel_left]
  have hlat : latSet I x' = latSet I x := by
    have h := h4 I x y k hk.1
    rwa [hxe] at h
  have hc1' : ∀ v u, coordV I x' v u = uMat (y v)⁻¹ *ᵥ coordV I x v u := by
    intro v u
    have h := coordV_mul I x y k v u
    rwa [hxe] at h
  have hc2' : ∀ v u, coordV I x v u = uMat (y v) *ᵥ coordV I x' v u := by
    intro v u
    have h := coordV_mul' I x y k v u
    rwa [hxe] at h
  refine ⟨fun s => ⟨subOfEq I hlat s, ?_⟩, fun s' => ⟨subOfEq I hlat.symm s', ?_⟩⟩
  · exact (size_subOfEq_le I h5 hlat _ hc1' hc1.le (fun v w => hbound _ (hy v).1 w) s).trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s))
  · exact (size_subOfEq_le I h5 hlat.symm _ hc2' hc1.le (fun v w => hbound _ (hy v).2 w) s').trans
      (mul_le_mul_of_nonneg_right hcN (size_nonneg I h5 s'))

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open Filter Topology

namespace Formalism.L2.SG.Pf.Tau

theorem t7 : InfimumContinuousFamily := by
  intro X _ S g hne hpos hloc
  have hbdd : ∀ x, BddBelow (Set.range (g x)) := fun x => ⟨0, by rintro _ ⟨s, rfl⟩; exact hpos x s⟩
  have hinf_nonneg : ∀ x, 0 ≤ ⨅ s, g x s := fun x => by
    haveI := hne x
    exact le_ciInf fun s => hpos x s
  have key : ∀ x y (r : ℝ), 0 ≤ r → (∀ s, ∃ s', g y s' ≤ r * g x s) → (⨅ s, g y s) ≤ r * ⨅ s, g x s := by
    intro x y r hr h
    haveI := hne x
    rw [Real.mul_iInf_of_nonneg hr]
    exact le_ciInf fun s => by
      obtain ⟨s', hs'⟩ := h s
      exact (ciInf_le (hbdd y) s').trans hs'
  have hmin : ∀ a b r : ℝ, 1 ≤ r → 0 ≤ b → a ≤ r * b → min (1 / 2) a ≤ r * min (1 / 2) b := by
    intro a b r hr hb hab
    rcases le_total b (1 / 2) with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans hab
    · rw [min_eq_left h]
      nlinarith [min_le_left (1 / 2 : ℝ) a]
  refine continuous_iff_continuousAt.2 fun x => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hr : (1 : ℝ) < 1 + ε := by linarith
  filter_upwards [hloc x (1 + ε) hr] with x' hx'
  have h1 := hmin _ _ _ hr.le (hinf_nonneg x) (key x x' _ (by linarith) hx'.1)
  have h2 := hmin _ _ _ hr.le (hinf_nonneg x') (key x' x _ (by linarith) hx'.2)
  have hm1 : min (1 / 2 : ℝ) (⨅ s, g x s) ≤ 1 / 2 := min_le_left _ _
  have hm2 : min (1 / 2 : ℝ) (⨅ s, g x' s) ≤ 1 / 2 := min_le_left _ _
  have hp1 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x s) := le_min (by norm_num) (hinf_nonneg x)
  have hp2 : 0 ≤ min (1 / 2 : ℝ) (⨅ s, g x' s) := le_min (by norm_num) (hinf_nonneg x')
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem one_le_norm_embedding_alt (I : AutInst) (a : 𝓞 I.E) (ha : a ≠ 0) :
    ∃ v, 1 ≤ ‖I.φ v (a : I.E)‖ := by
  set β : I.E := (a : I.E) * star (a : I.E) with hβ
  have hfix : star β = β := by simp [hβ, mul_comm]
  obtain ⟨γ, hγ⟩ := (I.cm.fixed β).1 hfix
  have haI : IsIntegral ℤ (a : I.E) := a.2
  have hsI : IsIntegral ℤ (star (a : I.E)) := IsIntegral.map I.cm.sig haI
  have hβI : IsIntegral ℤ β := haI.mul hsI
  have hγI : IsIntegral ℤ γ := by
    rw [← isIntegral_algebraMap_iff (algebraMap I.F I.E).injective, hγ]
    exact hβI
  have ha0 : (a : I.E) ≠ 0 := by simpa using ha
  have hβ0 : β ≠ 0 := mul_ne_zero ha0 (star_ne_zero.2 ha0)
  let g : 𝓞 I.F := ⟨γ, hγI⟩
  have hg0 : g ≠ 0 := by
    intro h
    apply hβ0
    rw [← hγ]
    have : γ = 0 := congrArg Subtype.val h
    simp [this]
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace I.F, 1 ≤ w (g : I.F) := by
    by_contra h
    push Not at h
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w₀) hg0 (fun z _ => h z)) (not_le.2 (h w₀))
  refine ⟨w, ?_⟩
  have e : w (g : I.F) = ‖I.φ w (a : I.E)‖ ^ 2 := by
    rw [← InfinitePlace.norm_embedding_eq, show (g : I.F) = γ from rfl, ← I.φ_over, hγ, hβ, map_mul,
      I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj, sq]
  rw [e] at hw
  by_contra h
  push Not at h
  nlinarith [norm_nonneg (I.φ w (a : I.E))]

theorem lattice_common_denominator (I : AutInst) : ∃ b : 𝓞 I.E, b ≠ 0 ∧
    ∀ y ∈ I.L, ∀ i, ∃ c : 𝓞 I.E, (c : I.E) = (b : I.E) * y i := by
  first | exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator .. | (apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> assumption) | (apply @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator I

theorem invertible_matrix_lower_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : Fin n → ℂ) (i : Fin n), ‖w i‖ ^ 2 ≤ C * ∑ k, ‖(A *ᵥ w) k‖ ^ 2 := by
  obtain ⟨U, rfl⟩ := hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  refine ⟨∑ i, ∑ k, ‖B i k‖ ^ 2 + 1, by positivity, fun w i => ?_⟩
  set z := (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ w
  have hw : w = B *ᵥ z := by
    simp only [z, B, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : ‖w i‖ ≤ ∑ k, ‖B i k‖ * ‖z k‖ := by
    rw [hw]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 : ‖w i‖ ^ 2 ≤ (∑ k, ‖B i k‖ ^ 2) * ∑ k, ‖z k‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ k, ‖B i k‖ ^ 2 ≤ ∑ i, ∑ k, ‖B i k‖ ^ 2 + 1 := by
    have := Finset.single_le_sum (f := fun i => ∑ k, ‖B i k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ i)
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))

theorem lattice_vectors_bounded_below (h0 : LatticeCommensurable) : LatticeVectorsBoundedBelow := by
  intro I x
  obtain ⟨m, hm1, hm, -⟩ := h0 I x
  obtain ⟨b, hb0, hb⟩ := lattice_common_denominator I
  have hC : ∀ v, ∃ C : ℝ, 0 < C ∧ ∀ (u : Fin I.n → I.E) (i : Fin I.n),
      ‖I.φ v (u i)‖ ^ 2 ≤ C * ∑ k, ‖coordV I x v u k‖ ^ 2 := fun v => by
    have hU : IsUnit (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) :=
      (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
    obtain ⟨C, hC, hCw⟩ := invertible_matrix_lower_bound _ hU
    exact ⟨C, hC, fun u i => hCw (fun i => I.φ v (u i)) i⟩
  choose C hCpos hCb using hC
  set K : ℝ := ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ ∑ v, ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v :=
      Finset.sum_nonneg fun w _ => by have := hCpos w; positivity
    linarith
  refine ⟨1 / K, by positivity, ?_⟩
  intro u hu hu0
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨c, hc⟩ := hb _ (hm u hu) i
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb0' : (b : I.E) ≠ 0 := by simpa using hb0
  have hc0 : c ≠ 0 := by
    intro h
    have : (c : I.E) = 0 := by simp [h]
    rw [hc, Pi.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero hb0' (mul_ne_zero hm0 hi) this
  obtain ⟨v, hv⟩ := one_le_norm_embedding_alt I c hc0
  have e : ‖I.φ v (c : I.E)‖ = ‖I.φ v (b : I.E)‖ * (m : ℝ) * ‖I.φ v (u i)‖ := by
    rw [hc, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_natCast, norm_mul, norm_mul,
      Complex.norm_natCast, mul_assoc]
  set S := ∑ w, ∑ k, ‖coordV I x w u k‖ ^ 2
  have hSv : ∑ k, ‖coordV I x v u k‖ ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => ∑ k, ‖coordV I x w u k‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ v)
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := by
    have : 1 ≤ ‖I.φ v (c : I.E)‖ ^ 2 := by nlinarith
    rw [e] at this
    nlinarith
  have h2 : ‖I.φ v (u i)‖ ^ 2 ≤ C v * S := (hCb v u i).trans
    (mul_le_mul_of_nonneg_left hSv (hCpos v).le)
  have h3 : ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v ≤ K := by
    have := Finset.single_le_sum (f := fun w => ‖I.φ w (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C w)
      (fun w _ => by have := hCpos w; positivity) (Finset.mem_univ v)
    linarith
  have h4 : 1 ≤ K * S := by
    have hbm : 0 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 := by positivity
    calc 1 ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * ‖I.φ v (u i)‖ ^ 2 := h1
      _ ≤ ‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * (C v * S) := mul_le_mul_of_nonneg_left h2 hbm
      _ = (‖I.φ v (b : I.E)‖ ^ 2 * (m : ℝ) ^ 2 * C v) * S := by ring
      _ ≤ K * S := mul_le_mul_of_nonneg_right h3 hS0
  rw [div_le_iff₀ hK0]
  linarith

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reduction_theory_of_lattice (h0 : LatticeCommensurable) (h8 : MinkowskiSubmodule) : ReductionTau :=
  reductionTau_of (third_estimate_of_first_two h0 (lattice_finitelyGenerated_of_commensurable h0)) (sizes_locally_comparable t4 t5) t7 h8 (lattice_vectors_bounded_below h0) (packet_conditions_closed (lattice_finitelyGenerated_of_commensurable h0) t2)

theorem reductionTau_of_minkowskiSubmodule (h8 : MinkowskiSubmodule) : ReductionTau :=
  reduction_theory_of_lattice t0 h8

end Formalism.L2.SG.Pf.Tau
end

section
set_option autoImplicit false

noncomputable section

open MeasureTheory Metric

namespace Formalism.L2.SG.Pf.Tau

theorem t8m : MinkowskiFirstTheorem := by
  intro d hd
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  set v1 : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hv1_def
  have hv1ne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hv1pos : 0 < v1 :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hv1ne
  refine ⟨4 / v1 ^ ((2 : ℝ) / d), by positivity, ?_⟩
  intro L _ _
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin d)))
  set F := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b) with hF_def
  have hcov : ZLattice.covolume L = volume.real F := ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hcov0 : 0 ≤ ZLattice.covolume L := by rw [hcov]; exact measureReal_nonneg
  have hFfin : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  set r : ℝ := 2 * (ZLattice.covolume L / v1) ^ ((1 : ℝ) / d) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ ZLattice.covolume L / v1 := by positivity
  have key : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ d = t := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  have key2 : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ 2 = t ^ ((2 : ℝ) / d) := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  have hrd : r ^ d = 2 ^ d * (ZLattice.covolume L / v1) := by
    rw [hr_def, mul_pow, key _ hq0]
  have hvol : volume F * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))
      ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [Measure.addHaar_closedBall volume 0 hr0, hfr, hrd, ← ENNReal.ofReal_toReal hv1ne, ← hv1_def,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hFfin]
    have : (volume F).toReal = ZLattice.covolume L := by rw [hcov]; rfl
    have e : (2 : ℝ) ^ d * (ZLattice.covolume L / v1) * v1 = ZLattice.covolume L * 2 ^ d := by
      field_simp
    rw [this, e, ENNReal.ofReal_mul hcov0, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  haveI hcL : Countable L := Countable.of_equiv _ b.repr.toEquiv.symm
  haveI : Countable L.toAddSubgroup := hcL
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hF (fun y hy => by simpa using hy) (convex_closedBall _ _)
    (isCompact_closedBall _ _) hvol
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), ?_⟩
  have hxr : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ r := by simpa using hxs
  calc ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
    _ = 4 / v1 ^ ((2 : ℝ) / d) * ZLattice.covolume L ^ ((2 : ℝ) / d) := by
      rw [hr_def, mul_pow, key2 _ hq0, Real.div_rpow hcov0 hv1pos.le]
      ring
  exact le_rfl

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Matrix Module MeasureTheory
open scoped ComplexOrder Classical

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

def t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * (Matrix.of fun i k => b k i).map (I.φ v)

theorem coord_linear_comb (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (a : Fin j → I.E) :
    coordV I x v (∑ k, a k • b k) = t8C I x v b *ᵥ fun k => I.φ v (a k) := by
  unfold coordV t8C
  have hw : (fun i => I.φ v ((∑ k, a k • b k) i)) =
      (Matrix.of fun i k => b k i).map (I.φ v) *ᵥ fun k => I.φ v (a k) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hw, Matrix.mulVec_mulVec]

theorem gramV_eq_conjTranspose_t8C_mul_t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (t8C I x v b)ᴴ * t8C I x v b := by
  have hc : ∀ a i, coordV I x v (b a) i = t8C I x v b i a := by
    intro a i
    first
      | rfl
      | (unfold coordV t8C; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply])
  unfold gramV
  ext a c
  simp only [hc, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem coord_matrix_mulVec_injective (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) :
    Function.Injective (t8C I x v b).mulVec := by
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  intro w w' h
  apply mulVec_injective_map (I.φ v) Bm hB
  apply Matrix.mulVec_injective_iff_isUnit.2 hAu
  simpa only [t8C, Matrix.mulVec_mulVec] using h

def linearCombinationOfRows {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) : (Fin j → E) →+ (Fin n → E) where
  toFun a := ∑ k, a k • b k
  map_zero' := by simp
  map_add' a a' := by simp [add_smul, Finset.sum_add_distrib]

theorem linearComb_apply {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (a : Fin j → E) :
    linearCombinationOfRows b a = ∑ k, a k • b k := rfl

theorem linear_comb_injective {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (hb : LinearIndependent E b) :
    Function.Injective (linearCombinationOfRows b) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [linearComb_apply] at ha
  funext k
  exact Fintype.linearIndependent_iff.mp hb a ha k

theorem linearComb_single {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (k : Fin j) (c : E) :
    linearCombinationOfRows b (Pi.single k c) = c • b k := by
  rw [linearComb_apply]
  simp [Pi.single_apply, ite_smul]

theorem short_vector_sublattice (I : AutInst) (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (x : I.GA) (s : Sub I x) (C : ℝ)
    (hC : ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ u ∈ L, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ C * ZLattice.covolume L ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ))) :
    ∃ u ∈ s.B, u ≠ 0 ∧ ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2 ≤
      C * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) * size I s ^ 2 := by

  choose R hR hRdet using fun v => gram_factor_invertible (t8C I x v s.b) (coord_matrix_mulVec_injective I x v s.b s.b_ind)
  have hgram : ∀ v, (gramV I x v s.b).det.re = Complex.normSq (R v).det := by
    intro v
    rw [gramV_eq_conjTranspose_t8C_mul_t8C, hR v, Matrix.det_mul, Matrix.det_conjTranspose,
      ← Complex.ofReal_re (Complex.normSq (R v).det), Complex.normSq_eq_conj_mul_self]
    rfl

  set P : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) (Set.range s.b) with hP
  have hfin : Finite (s.B ⧸ P.comap s.B.subtype) := by
    obtain ⟨M, hMfg, hM⟩ := h1 I x
    refine h2 I.E I.n s.j M s.B s.b hMfg ?_ s.b_ind s.b_mem s.B_span
    intro u hu
    rw [← SetLike.mem_coe, hM]
    exact s.B_lat hu
  set N : ℕ := Nat.card (s.B ⧸ P.comap s.B.subtype) with hN
  have hN0 : 0 < N := Nat.card_pos

  set lin := linearCombinationOfRows s.b with hlin
  have hlinj : Function.Injective lin := linear_comb_injective s.b s.b_ind
  set Bp : AddSubgroup (Fin s.j → I.E) := s.B.toAddSubgroup.comap lin with hBp
  set Op : AddSubgroup (Fin s.j → I.E) := (t8O I s.j).toAddSubgroup with hOp
  have hgen : ∀ p : Σ _ : Fin s.j, Free.ChooseBasisIndex ℤ (𝓞 I.E),
      lin (Pi.single p.1 (integralBasis I.E p.2)) = (RingOfIntegers.basis I.E p.2) • s.b p.1 := by
    intro p
    rw [hlin, linearComb_single, integralBasis_apply, algebraMap_smul]
  have hOB : Op ≤ Bp := by
    intro y hy
    change lin y ∈ s.B
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      rw [hgen]
      exact s.B.smul_mem _ (s.b_mem p.1)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact s.B.add_mem hy hz
    | smul c y _ hy => rw [map_zsmul]; exact s.B.toAddSubgroup.zsmul_mem hy c
  have hmapO : Op.map lin = P.toAddSubgroup := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      change lin a ∈ P
      induction ha using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        rw [hgen]
        exact P.smul_mem _ (Submodule.subset_span ⟨p.1, rfl⟩)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact P.add_mem hy hz
      | smul c y _ hy => rw [map_zsmul]; exact P.toAddSubgroup.zsmul_mem hy c
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 I.E)).1 (show y ∈ P from hy)
      refine ⟨fun k => (c k : I.E), mem_integral_vectors I s.j _ fun k => ⟨c k, rfl⟩, ?_⟩
      rw [hlin, linearComb_apply, ← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact algebraMap_smul I.E (c k) (s.b k)
  have hmapB : Bp.map lin = s.B.toAddSubgroup := by
    refine AddSubgroup.map_comap_eq_self ?_
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (s.B_span hu)
    exact ⟨c, hc⟩
  have hrel : Op.relIndex Bp = N := by
    rw [← AddSubgroup.relIndex_map_map_of_injective Op Bp hlinj, hmapO, hmapB, hN]
    rfl

  have hRdet' : ∀ v, (R v).det ≠ 0 := hRdet
  set Θ := t8Th R with hΘ
  have hΘinj : Function.Injective Θ := blockTransform_injective R hRdet'
  set L₁ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    Submodule.span ℤ (Set.range (blockBasis R hRdet')) with hL₁
  set L₂ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    (Bp.map Θ).toIntSubmodule with hL₂
  have hL₁' : L₁.toAddSubgroup = Op.map Θ := by
    rw [hL₁, ← map_integral_vectors_span R hRdet']
    rfl
  have hL₂' : L₂.toAddSubgroup = Bp.map Θ := AddSubgroup.toIntSubmodule_toAddSubgroup _
  have h12 : L₁ ≤ L₂ := by
    intro y hy
    have hy' : y ∈ L₁.toAddSubgroup := hy
    rw [hL₁'] at hy'
    show y ∈ L₂.toAddSubgroup
    rw [hL₂']
    exact AddSubgroup.map_mono hOB hy'
  have hrel2 : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup = N := by
    rw [hL₁', hL₂', AddSubgroup.relIndex_map_map_of_injective Op Bp hΘinj, hrel]

  have hNR : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN0.ne')
  set β' := (blockBasis R hRdet').isUnitSMul (w := fun _ => ((N : ℝ))⁻¹) (fun _ => isUnit_iff_ne_zero.2 hNR)
    with hβ'
  have hsub : (L₂ : Set (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) ⊆ Submodule.span ℤ (Set.range β') := by
    intro w hw
    have hw' : w ∈ L₂.toAddSubgroup := hw
    rw [hL₂'] at hw'
    obtain ⟨a, ha, rfl⟩ := hw'
    have hNa : N • a ∈ Op := by
      rw [← hrel]
      exact AddSubgroup.nsmul_relIndex_mem Op ha
    have hNw : N • Θ a ∈ L₁ := by
      have : Θ (N • a) ∈ L₁.toAddSubgroup := by
        rw [hL₁']
        exact ⟨N • a, hNa, rfl⟩
      rwa [map_nsmul] at this
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hNw
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
    simp only [hβ', Basis.isUnitSMul_apply]
    have e : ∀ p, c p • ((N : ℝ)⁻¹ • blockBasis R hRdet' p) = (N : ℝ)⁻¹ • (c p • blockBasis R hRdet' p) :=
      fun p => smul_comm _ _ _
    simp only [e, ← Finset.smul_sum, hc]
    rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0.ne')]
  have : DiscreteTopology L₂ :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range β'))) hsub
  have : IsZLattice ℝ L₂ := ⟨by
    rw [eq_top_iff, ← (blockBasis R hRdet').span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    exact h12 (Submodule.subset_span ⟨p, rfl⟩)⟩

  have hcov := ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h12
  rw [hrel2, covolume_blockBasis] at hcov
  have hht : ht I s = (∏ v, Complex.normSq (R v).det) / N := by
    rw [ht]
    simp only [hgram]
    rfl
  have hcov2 : ZLattice.covolume L₂ = t8K I s.j * ht I s := by
    have hpos := ZLattice.covolume_pos L₂ volume
    rw [hht]
    rw [div_eq_iff hpos.ne'] at hcov
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    field_simp
    linarith
  have hht0 : 0 ≤ ht I s := by
    rw [hht]
    exact div_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

  obtain ⟨w, hw, hw0, hwb⟩ := hC L₂
  have hw' : w ∈ L₂.toAddSubgroup := hw
  rw [hL₂'] at hw'
  obtain ⟨a, ha, rfl⟩ := hw'
  refine ⟨lin a, ha, ?_, ?_⟩
  · intro h0
    apply hw0
    have : a = 0 := hlinj (by rw [h0, map_zero])
    rw [this, map_zero]
  · have hnorm : ‖Θ a‖ ^ 2 = ∑ v, ∑ i, ‖coordV I x v (lin a) i‖ ^ 2 := by
      rw [hΘ, blockTransform_norm_sq]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hlin, linearComb_apply, coord_linear_comb]
      exact (norm_sq_eq_of_gram_eq _ _ (hR v) _).symm
    rw [← hnorm]
    refine hwb.trans (le_of_eq ?_)
    rw [hcov2, Real.mul_rpow (integral_covolume_pos I s.j).le hht0, size, ← Real.rpow_mul_natCast hht0]
    have hf : (0 : ℝ) < I.f := by
      have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
      rw [card_infinite_places] at this
      exact_mod_cast this
    have hj : (0 : ℝ) < s.j := by exact_mod_cast s.j_pos
    have e : (1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)) * ((2 : ℕ) : ℝ) = (2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e]
    ring

theorem minkowski_submodule_short_vector (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (h8m : MinkowskiFirstTheorem) : MinkowskiSubmodule := by
  intro I
  let cj : ℕ → ℝ := fun j =>
    if h : 1 ≤ 2 * I.f * j then (h8m _ h).choose * t8K I j ^ ((2 : ℝ) / ((2 * I.f * j : ℕ) : ℝ)) else 0
  have hcj : ∀ j, 0 ≤ cj j := by
    intro j
    simp only [cj]
    split_ifs with h
    · exact mul_nonneg (h8m _ h).choose_spec.1.le (Real.rpow_nonneg (integral_covolume_pos I j).le _)
    · exact le_rfl
  refine ⟨1 + ∑ j ∈ Finset.range (I.n + 1), cj j, by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range (I.n + 1)) => hcj j
    linarith, ?_⟩
  intro x s
  have hd : 1 ≤ 2 * I.f * s.j := by
    have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
    rw [card_infinite_places] at this
    have := s.j_pos
    have : 1 ≤ I.f * s.j := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [Nat.mul_assoc]
    omega
  obtain ⟨u, hu, hu0, hub⟩ := short_vector_sublattice I h1 h2 x s (h8m _ hd).choose (fun L _ _ => (h8m _ hd).choose_spec.2 L)
  refine ⟨u, hu, hu0, hub.trans ?_⟩
  have hjn : s.j ≤ I.n := by
    have := s.b_ind.fintype_card_le_finrank
    simpa using this
  have hle : cj s.j ≤ 1 + ∑ j ∈ Finset.range (I.n + 1), cj j := by
    have := Finset.single_le_sum (f := cj) (fun j _ => hcj j) (Finset.mem_range.2 (Nat.lt_succ_of_le hjn))
    linarith
  have hcs : cj s.j = (h8m _ hd).choose * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) := by
    simp only [cj, dif_pos hd]
  rw [← hcs]
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

end Formalism.L2.SG.Pf.Tau
end
end

section
set_option autoImplicit false

namespace Formalism.L2.SG.Pf.Tau

theorem reductionTau : ReductionTau :=
  reductionTau_of_minkowskiSubmodule (minkowski_submodule_short_vector (lattice_finitelyGenerated_of_commensurable t0) t2 t8m)

end Formalism.L2.SG.Pf.Tau
end
