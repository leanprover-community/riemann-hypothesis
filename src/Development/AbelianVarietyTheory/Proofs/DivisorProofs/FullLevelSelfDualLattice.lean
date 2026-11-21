import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLiftInThetaGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteFrameRealSpecialUnitary

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem host_unr : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE;
    GlobalTheory.UCls.Unr D.host.E := fun D =>
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  Formalism.L2.Pj.unramBridge_holds D.host.E (Formalism.L2.Pj.cmUnram_conj D)

end GlobalTheory.MassLink
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_class_of_cm_host : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.Unr D.host.E := by
  atlas_forward_decl GlobalTheory.MassLink.host_unr
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_from_conjugate_complement : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; (∀ τ : D.host.E →+* ℂ, τ ∈ GlobalTheory.MassLink.psi D ↔ ComplexEmbedding.conjugate τ ∉ GlobalTheory.MassLink.psi D) ∧ ∃ eΨ : D.what₂.Tau ≃ GlobalTheory.MassLink.psi D, ∀ ρ, ((eΨ ρ : GlobalTheory.MassLink.psi D) : D.host.E →+* ℂ) = TH.tauE D ρ := by
  first | exact @GlobalTheory.MassLink.psi_cmType_equiv | exact GlobalTheory.MassLink.psi_cmType_equiv | (intros; apply GlobalTheory.MassLink.psi_cmType_equiv <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrthFrames

open Matrix
open scoped ComplexConjugate

theorem exists_perm_initial {r : ℕ} (P : Fin r → Prop) [DecidablePred P] :
    ∃ (σ : Equiv.Perm (Fin r)) (p : ℕ), ∀ a, P (σ a) ↔ (a : ℕ) < p := by
  classical
  let f : Fin r → ℕ := fun a => if P a then 0 else 1
  let σ := Tuple.sort f
  have hm : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let S : Finset (Fin r) := Finset.univ.filter fun a => f (σ a) = 0
  refine ⟨σ, S.card, fun a => ?_⟩
  have hP : P (σ a) ↔ f (σ a) = 0 := by
    simp only [f]; split_ifs with h <;> simp [h]
  rw [hP]
  constructor
  · intro h0
    have hsub : Finset.Iic a ⊆ S := by
      intro b hb
      rw [Finset.mem_Iic] at hb
      have := hm hb
      simp only [Function.comp_apply] at this
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra h0
    have hsub : S ⊆ Finset.Iio a := by
      intro b hb
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.mem_Iio]
      by_contra hba
      have := hm (not_lt.1 hba)
      simp only [Function.comp_apply] at this
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem exists_sgn_frame {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (hN : N.IsHermitian) (hd : N.det ≠ 0) :
    ∃ (X : Matrix (Fin r) (Fin r) ℂ) (p : ℕ),
      Xᴴ * N * X = diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  classical
  set U : Matrix (Fin r) (Fin r) ℂ := (hN.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hUdef
  set lam := hN.eigenvalues with hlam
  have hU : Uᴴ * N * U = diagonal fun k => ((lam k : ℝ) : ℂ) := by
    have h := hN.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [hUdef, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h ⊢
    rw [h]; rfl
  have hne : ∀ k, lam k ≠ 0 := by
    intro k hk
    apply hd
    rw [hN.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [← hlam, hk])
  obtain ⟨σ, p, hσ⟩ := exists_perm_initial fun k => 0 < lam k
  let s : Fin r → ℝ := fun a => (Real.sqrt |lam (σ a)|)⁻¹
  let Y : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun k a => if k = σ a then ((s a : ℝ) : ℂ) else 0
  refine ⟨U * Y, p, ?_⟩
  have e1 : (U * Y)ᴴ * N * (U * Y) = Yᴴ * (Uᴴ * N * U) * Y := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, hU]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Y, Matrix.of_apply, diagonal_apply]
  rw [Finset.sum_eq_single (σ a)]
  · by_cases hab : a = b
    · subst hab
      simp only [if_true, Complex.star_def, Complex.conj_ofReal]
      have hs : s a * lam (σ a) * s a = ReciprocityTheory.ChartRestriction.G.FD.sgn p a := by
        have habs : 0 < |lam (σ a)| := abs_pos.2 (hne _)
        have hsq : s a * s a = |lam (σ a)|⁻¹ := by
          simp only [s]
          rw [← mul_inv, Real.mul_self_sqrt habs.le]
        unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
        by_cases hpos : 0 < lam (σ a)
        · rw [if_pos ((hσ a).1 hpos)]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = 1 := by rw [hsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
        · have hneg : lam (σ a) < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hne _)
          rw [if_neg (fun h => hpos ((hσ a).2 h))]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = -1 := by
              rw [hsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hneg.ne]
      rw [← hs]; push_cast; ring
    · have : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [this, hab]
  · intro k _ hk
    simp [hk]
  · simp

theorem gram_eq_transpose {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.OrthFrames

namespace GlobalTheory.OrthFrames

open Matrix

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) :
    V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem gm_isHermitian (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).IsHermitian := by
  haveI hcm : IsCMField D.host.E := D.host.isCMField_hostE
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MassLink.gm, Matrix.submatrix_apply, HSpace.gram]
  rw [← (Wc D i).herm.eq ((Wc D i).frame (Fin.cast (rank_Wc i).symm b))]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem gm_det_ne (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).det ≠ 0 := by
  rw [Matrix.det_transpose]
  have e := RingHom.map_det τ (GlobalTheory.MassLink.gm D i)
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, map_ne_zero]
  simp only [GlobalTheory.MassLink.gm, Matrix.det_transpose]
  have e2 : (HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
      (HSpace.gram (Wc D i)).submatrix (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm) := rfl
  rw [e2, Matrix.det_submatrix_equiv_self]
  exact hspace_gram_det_ne _

theorem exists_orth_frames : ∀ (D : D7) (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∃ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (GlobalTheory.MassLink.psi D) D.R.r) (p0 : GlobalTheory.MassLink.psi D → ℕ),
      ∀ τ : GlobalTheory.MassLink.psi D, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := by
  intro D i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have key : ∀ τ : GlobalTheory.MassLink.psi D, ∃ (X : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (p : ℕ),
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) X =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    obtain ⟨X, p, hX⟩ := exists_sgn_frame _ (gm_isHermitian D i τ.1) (gm_det_ne D i τ.1)
    refine ⟨X, p, ?_⟩
    rw [gram_eq_transpose, hX, Matrix.diagonal_transpose]
  choose X p hX using key
  exact ⟨fun τ => X τ, p, fun τ => hX τ⟩

end GlobalTheory.OrthFrames
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_of_mass_frame_diagonal : ∀ (D : D7) (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (GlobalTheory.MassLink.psi D) D.R.r) (p0 : GlobalTheory.MassLink.psi D → ℕ), ∀ τ : GlobalTheory.MassLink.psi D, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := by
  atlas_forward_decl GlobalTheory.OrthFrames.exists_orth_frames
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_of_level_class : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.SelfDualLat (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i) := by
  first | exact @GlobalTheory.MassLinkSD.base_selfDualLat | exact GlobalTheory.MassLinkSD.base_selfDualLat | (intros; apply GlobalTheory.MassLinkSD.base_selfDualLat <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SURepsExist

open Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem isUA_mul {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (hg' : IsUA c G g') :
    IsUA c G (g * g') := by
  refine ⟨by rw [det_mul]; exact hg.1.mul hg'.1, fun x y => ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hg'.2]

theorem isUA_of_inv {g g' : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsUA c G g) (h1 : g * g' = 1) :
    IsUA c G g' := by
  refine ⟨IsUnit.of_mul_eq_one g.det (by rw [mul_comm, ← det_mul, h1, det_one]), fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, h1, one_mulVec, one_mulVec]

variable {L : Set (Fin n → E)}

theorem stabilizer_maps_lattice_completion {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) {x : Fin n → RA F E}
    (hx : x ∈ hat F L) : k *ᵥ x ∈ hat F L := by
  obtain ⟨y, hy, e⟩ := hk.2.1 x hx
  rw [one_nsmul, sub_eq_iff_eq_add] at e
  rw [e]; exact (hat F L).add_mem hy hx

theorem stabilizer_of_maps_onto {k : Matrix (Fin n) (Fin n) (RA F E)} (hU : IsUA c G k)
    (hm : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L) (hs : ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x) :
    IsKM c G L 1 k :=
  ⟨hU, fun x hx => ⟨k *ᵥ x - x, (hat F L).sub_mem (hm x hx) hx, by rw [one_nsmul]⟩, hs⟩

theorem stabilizer_mul {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (hk' : IsKM c G L 1 k') :
    IsKM c G L 1 (k * k') := by
  refine stabilizer_of_maps_onto c G (isUA_mul c G hk.1 hk'.1) (fun x hx => ?_) (fun x hx => ?_)
  · rw [← mulVec_mulVec]; exact stabilizer_maps_lattice_completion c G hk (stabilizer_maps_lattice_completion c G hk' hx)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, rfl⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [mulVec_mulVec]⟩

theorem stabilizer_inv {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L 1 k) (h1 : k * k' = 1)
    (h2 : k' * k = 1) : IsKM c G L 1 k' := by
  refine stabilizer_of_maps_onto c G (isUA_of_inv c G hk.1 h1) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    rwa [mulVec_mulVec, h2, one_mulVec]
  · exact ⟨k *ᵥ x, stabilizer_maps_lattice_completion c G hk hx, by rw [mulVec_mulVec, h2, one_mulVec]⟩

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E))

theorem isSA_mul {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (hg' : IsSA G g') : IsSA G (g * g') :=
  ⟨isUA_mul _ G hg.1 hg'.1, by rw [det_mul, hg.2, hg'.2, one_mul]⟩

theorem isSA_of_inv {g g' : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)} (hg : IsSA G g)
    (h1 : g * g' = 1) : IsSA G g' :=
  ⟨isUA_of_inv _ G hg.1 h1, by
    have := congrArg Matrix.det h1
    rwa [det_mul, hg.2, one_mul, det_one] at this⟩

theorem ratM_inv (γ : Matrix (Fin r) (Fin r) E) (hγ : IsSA G (ratM (maximalRealSubfield E) γ)) :
    ratM (maximalRealSubfield E) γ * ratM (maximalRealSubfield E) γ⁻¹ = 1 ∧
    ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ = 1 := by
  by_cases h : γ.det = 0
  · have e : (ratM (maximalRealSubfield E) γ).det = 0 := by
      have := (Algebra.TensorProduct.includeRight :
        E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).map_det γ
      rw [h, map_zero] at this
      exact this.symm
    rw [hγ.2] at e
    haveI : Subsingleton (RA (maximalRealSubfield E) E) := subsingleton_of_zero_eq_one e.symm
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · have hu : IsUnit γ.det := isUnit_iff_ne_zero.mpr h
    rw [← ratM_mul, ← ratM_mul, mul_nonsing_inv γ hu, nonsing_inv_mul γ hu, ratM_one]
    exact ⟨rfl, rfl⟩

def sSetoid : Setoid {g // IsSA G g} where
  r a b := SEquiv G L 1 a.1 b.1
  iseqv := by
    refine ⟨fun a => ⟨1, by rw [ratM_one]; exact ⟨⟨by simp, fun x y => by simp⟩, by simp⟩,
      1, isKM_one _ G L 1, by simp, by rw [ratM_one]; simp⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, k, hk, hdk, e⟩
      have hr := ratM_inv G γ hγ
      have hku : IsUnit k.det := by rw [hdk]; exact isUnit_one
      refine ⟨γ⁻¹, isSA_of_inv G hγ hr.1, k⁻¹, stabilizer_inv _ G hk (mul_nonsing_inv k hku)
        (nonsing_inv_mul k hku), ?_, ?_⟩
      · rw [det_nonsing_inv, hdk, Ring.inverse_one]
      · rw [e]
        calc a.1 = (ratM (maximalRealSubfield E) γ⁻¹ * ratM (maximalRealSubfield E) γ) * a.1 * (k * k⁻¹) := by
                rw [hr.2, mul_nonsing_inv k hku]; simp
          _ = _ := by simp only [Matrix.mul_assoc]
    · rintro a b d ⟨γ, hγ, k, hk, hdk, e⟩ ⟨γ', hγ', k', hk', hdk', e'⟩
      refine ⟨γ' * γ, by rw [ratM_mul]; exact isSA_mul G hγ' hγ, k * k', stabilizer_mul _ G hk hk',
        by rw [det_mul, hdk, hdk', one_mul], ?_⟩
      rw [e', e, ratM_mul]; simp only [Matrix.mul_assoc]

theorem exists_sReps : ∃ (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)),
    IsSReps G L 1 s := by
  letI := sSetoid G L
  refine ⟨Quotient (sSetoid G L), fun q => q.out.1, fun q => q.out.2, fun i j h => ?_, fun g hg => ?_⟩
  · rw [← Quotient.out_eq i, ← Quotient.out_eq j]
    exact Quotient.sound h
  · exact ⟨⟦⟨g, hg⟩⟧, Quotient.mk_out (s := sSetoid G L) ⟨g, hg⟩⟩

end CM

end GlobalTheory.SURepsExist

theorem GlobalTheory.SURepsExist.main : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s := by
  intro D Tu Cl t0 _ i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  exact GlobalTheory.SURepsExist.exists_sReps _ _
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_representatives_exist : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s := by
  atlas_forward_decl GlobalTheory.SURepsExist.main
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_representatives_theta_compatible : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s → ∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i (s j'))⁻¹ * g * GlobalTheory.MassLink.lift D i (s j)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j') := by
  first | exact @GlobalTheory.MassLinkConj.main | exact GlobalTheory.MassLinkConj.main | (intros; apply GlobalTheory.MassLinkConj.main <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hat_iff_swap {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h

theorem core {n r : ℕ} (h : n = r) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hF : Formalism.L2.DIV.IsFrame β Λ)
    (S K G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hSK : S * K = G * S)
    (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hk : k.val = K.map (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E))
    (hkS : k ∈ Formalism.L2.DIV.St β) (s A : Matrix (Fin r) (Fin r) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (hs : S = s.submatrix (Fin.cast h) (Fin.cast h)) (hA : G = A.submatrix (Fin.cast h) (Fin.cast h)) :
    ∀ y ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)), A *ᵥ (s *ᵥ y) = s *ᵥ y' := by
  subst h
  have e : Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast (rfl : n = n))) = Λ := by
    ext x
    simp only [Submodule.mem_comap, Fin.cast_refl]
    exact Iff.rfl
  simp only [Fin.cast_refl, submatrix_id_id] at hs hA
  subst hs hA
  rw [e]
  intro y hy
  refine ⟨K *ᵥ y, ?_, ?_⟩
  · rw [mem_hat_iff_swap] at hy ⊢
    have h1 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hkS _).1 hy
    convert h1 using 1
    funext i
    rw [hk]
    exact RingHom.map_mulVec (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingHom K y i
  · rw [mulVec_mulVec, mulVec_mulVec, hSK]

end General

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem inclAF_injective (D : D7) :
    Function.Injective (GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (E := D.host.E) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mem_UJ_of_GQ (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (hg : g ∈ GQ V)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h1 : matHom V g ∈ GlobalTheoryTheory.GenusMassVolumes.HFin (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := hg
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 h1
  have e2 : Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) x =
      Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ := e.trans hm
  have : x = γ := by
    refine Units.ext (Matrix.ext fun a b => inclAF_injective D ?_)
    have := congrArg (fun M : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E) =>
      M.1 a b) e2
    simpa [Formalism.UG.bc] using this
  exact this ▸ hx

theorem finHom_val_of_mat (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    (finHom V g).val = (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (fun x => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x) := by
  have : (finHom V g).val = ((matHom V g).val).map
      (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  rw [this, hm]
  ext a b
  simp [Formalism.UG.bc, GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

example (D : D7) (x : D.host.E) : letI : IsCMField D.host.E := D.host.isCMField_hostE;
    D.sp.cm.sig x = IsCMField.complexConj D.host.E x := rfl

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y =
      (fun b => (IsCMField.complexConj E : E →+* E) (y b)) ⬝ᵥ (J *ᵥ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  ring

theorem herm_unitary {n r : ℕ} (h : n = r) (J γ : Matrix (Fin n) (Fin n) E)
    (hγ : Formalism.UG.cT (IsCMField.complexConj E : E →+* E) γ * J * γ = J) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ
        (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ x) (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ y) =
      ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ x y := by
  subst h
  simp only [Fin.cast_refl, submatrix_id_id]
  rw [herm_transpose, herm_transpose]
  have key : (fun b => (IsCMField.complexConj E : E →+* E) ((γ *ᵥ y) b)) =
      γ.map (IsCMField.complexConj E : E →+* E) *ᵥ (fun b => (IsCMField.complexConj E : E →+* E) (y b)) := by
    funext b
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [key, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec, mulVec_mulVec]
  have hγ' : (γ.map (IsCMField.complexConj E : E →+* E))ᵀ * J * γ = J := hγ
  rw [hγ']

end Herm

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem fwd (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu) (hCl : Cl.Is t0) (i : Fin D.R.m)
    (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
    (hlift : ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)))
    (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E)
    (hm : matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ)
    (hγr : (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E))
    (hk : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) :
    ∀ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
        GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E) (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (s *ᵥ y) =
          s *ᵥ y' := by
  obtain ⟨c, hc⟩ := hCl.βW i
  set h := GlobalTheory.MassLink.lift D i s with hh
  have hSK : (finHom (Wc D i) h).val * (finHom (Wc D i) (h⁻¹ * g * h)).val =
      (finHom (Wc D i) g).val * (finHom (Wc D i) h).val := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have hA : (finHom (Wc D i) g).val = (GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E)
      (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)).submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
    rw [finHom_val_of_mat D (Wc D i) g γ hm, ← hγr]
    ext a b
    simp [GlobalTheory.UCls.ratM]
  exact core (F := D.host.F) (rank_Wc i) (Cl.ΛW i) (Cl.βW i) hc.1 _ _ _ hSK
    (Formalism.IndefR.Lev.finE (Wc D i) (h⁻¹ * g * h)) rfl (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk)) s _
    hlift hA

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_of_lift : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) →
    ∀ (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ GQ (Wc D i) → matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hlift g γ γr hg hm hγr hdet hk
  refine ⟨hdet, fun x y => ?_, fun x => ?_⟩
  · have hU := mem_UJ_of_GQ D (Wc D i) g γ hg hm
    have := herm_unitary (rank_Wc i) (Wc D i).gram (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E)
      hU x y
    rw [hγr] at this
    exact this
  · have hm' : matHom (Wc D i) g⁻¹ = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ⁻¹ := by
      rw [map_inv, hm, map_inv]
    have hγr' : ((γ⁻¹ : GL (Fin (Wc D i).rank) D.host.E) : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix
        (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
        ((γr⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) := by
      rw [Matrix.coe_units_inv, Matrix.coe_units_inv, ← hγr]
      exact (Matrix.inv_submatrix_equiv _ (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm)).symm
    have hk' : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) := by
      have e : (GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s =
          ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s)⁻¹ := by group
      rw [e, map_inv]
      exact inv_mem hk
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g⁻¹ γ⁻¹ γr⁻¹ hm' hγr' hk' y hy
      refine ⟨y', hy', ?_⟩
      rw [← e, hxy, mulVec_mulVec, ← GlobalTheory.SUVol.ratM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        GlobalTheory.SUVol.ratM_one, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g γ γr hm hγr hk y hy
      exact ⟨y', hy', e.symm⟩

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_mem : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s →
    ∀ (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hs
  exact ratStab_of_lift D Tu Cl t0 hCl i s (GlobalTheory.T.special_unitary_lift_in_theta_group D i s hs).2

end GlobalTheory.MassLink.StabLink
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_rational_matrix_compatible : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s → ∀ (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  atlas_forward_decl GlobalTheory.MassLink.StabLink.ratStab_mem
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem data_link : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) ∧ (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) := by
  intro D Tu Cl t0 hCl i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, eΨ, heΨ⟩ := GlobalTheory.T.cm_type_from_conjugate_complement D
  obtain ⟨x, p0, hx⟩ := GlobalTheory.T.gram_matrix_of_mass_frame_diagonal D i
  obtain ⟨J, s, hs⟩ := GlobalTheory.T.special_unitary_representatives_exist D Tu Cl t0 hCl i
  refine ⟨gm D i, lat Cl i, psi D, x, p0, J, s, fun j => lift D i (s j),
    ⟨(GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).1, GlobalTheory.T.unramified_class_of_cm_host D, GlobalTheory.T.self_dual_lattice_of_level_class D Tu Cl t0 hCl i, hcm, hx, hs, (GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).2⟩, rfl,
    ⟨eΨ, heΨ⟩, fun j => (GlobalTheory.T.special_unitary_lift_in_theta_group D i (s j) (hs.1 j)).1, GlobalTheory.T.special_unitary_representatives_theta_compatible D Tu Cl t0 hCl i J s hs,
    fun j g γ γr hg hm hr hd hk => GlobalTheory.T.special_unitary_rational_matrix_compatible D Tu Cl t0 hCl i (s j) (hs.1 j) g γ γr hg hm hr hd hk⟩

end GlobalTheory.MassLink
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovolNegFrame
open GlobalTheory.FrameIndep
open scoped InnerProductSpace ComplexConjugate

abbrev dgM {r : ℕ} (d : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => (d a : ℂ)

theorem dgM_mul {r : ℕ} {d : Fin r → ℝ} (hd : ∀ a, d a * d a = 1) : dgM d * dgM d = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; rw [← Complex.ofReal_mul, hd]; simp

theorem dgM_transpose {r : ℕ} (d : Fin r → ℝ) : (dgM d)ᵀ = dgM d := Matrix.diagonal_transpose _

theorem cj_dgM {r : ℕ} (d : Fin r → ℝ) : cj (dgM d) = dgM d := by
  ext a b; by_cases h : a = b <;> simp [h, Matrix.diagonal_apply]

theorem frame_facts_dg {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℝ) (hd : ∀ a, d a * d a = 1) (h : gram τ G M = dgM d) :
    M * M⁻¹ = 1 ∧ M⁻¹ * M = 1 ∧ (M⁻¹)ᵀ * dgM d * cj (M⁻¹) = G.map τ := by
  rw [gram_eq] at h
  have h1 : Mᵀ * (G.map τ * cj M * dgM d) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, dgM_mul hd]
  have hu : IsUnit M.det := by
    have := Matrix.isUnit_det_of_right_inverse h1
    rwa [Matrix.det_transpose] at this
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  refine ⟨hMi, hiM, ?_⟩
  have c1 : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMi, Matrix.transpose_one]
  have c2 : cj M * cj (M⁻¹) = 1 := by rw [← cj_mul, hMi]; simp
  rw [← h]
  calc (M⁻¹)ᵀ * (Mᵀ * G.map τ * cj M) * cj M⁻¹ = ((M⁻¹)ᵀ * Mᵀ) * G.map τ * (cj M * cj M⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = G.map τ := by rw [c1, c2, Matrix.one_mul, Matrix.mul_one]

theorem inner_theta_dg {ι : Type} [Fintype ι] {r : ℕ} (d : ι → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (Y Z : WW ι r) (hY : ∀ t, IsSkew (dgM (d t)) (blk Y t)) :
    ⟪cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y, Z⟫_ℝ = -(∑ t, (blk Y t * blk Z t).trace).re := by
  have key : ∀ t a b, (starRingEnd ℂ) ((d t a : ℂ) * Y (t, a, b) * (d t b : ℂ)) = -(Y (t, b, a)) := by
    intro t a b
    have h := congrArg (fun A : Matrix (Fin r) (Fin r) ℂ => A a b) (hY t)
    simp only [IsSkew, dgM, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.map_apply, FrameIndep.blk, Matrix.of_apply, Matrix.zero_apply] at h
    have hb : (d t b : ℂ) * d t b = 1 := by rw [← Complex.ofReal_mul, hd]; simp
    rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    linear_combination (d t b : ℂ) * h - Y (t, b, a) * hb
  have hc : ∀ u w : ℂ, ⟪u, w⟫_ℝ = ((starRingEnd ℂ) u * w).re := fun u w => by
    rw [Complex.inner, mul_comm]
  have hs : ∑ i, (starRingEnd ℂ) (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y i) * Z i =
      -∑ t, (blk Y t * blk Z t).trace := by
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) (t, a, b) =
        (d t a : ℂ) * Y (t, a, b) * (d t b : ℂ) := by
      intro a b
      simp [cjW, FrameIndep.blk, dgM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [e, key, Matrix.trace, Matrix.diag, Matrix.mul_apply, FrameIndep.blk, Matrix.of_apply,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [PiLp.inner_apply]
  simp only [hc]
  rw [← Complex.re_sum, hs, Complex.neg_re]

theorem mem_comap_iff_dg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (d : Ψ → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = dgM (d τ)) (Y : WW Ψ r) :
    Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ ∀ τ : Ψ, (blk Y τ).trace = 0 ∧ IsSkew (dgM (d τ)) (blk Y τ) := by
  rw [Submodule.mem_comap]
  show (∀ τ : Ψ, (Matrix.of (fromFrame x Y τ)).trace = 0 ∧ ∀ u w,
    hermC τ.1 G (Matrix.of (fromFrame x Y τ) *ᵥ u) w + hermC τ.1 G u (Matrix.of (fromFrame x Y τ) *ᵥ w) = 0) ↔ _
  refine forall_congr' fun τ => ?_
  obtain ⟨h1, h2, h3⟩ := frame_facts_dg τ.1 G (mat x τ) (d τ) (hd τ) (hx τ)
  have e : Matrix.of (fromFrame x Y τ) = mat x τ * blk Y τ * (mat x τ)⁻¹ := rfl
  rw [e, herm_skew_iff, trace_conj h2]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · have := isSkew_conj h1 h2 h3 h
    have e2 : (mat x τ)⁻¹ * (mat x τ * blk Y τ * (mat x τ)⁻¹) * mat x τ = blk Y τ := by
      calc _ = ((mat x τ)⁻¹ * mat x τ) * blk Y τ * ((mat x τ)⁻¹ * mat x τ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp
    rwa [e2] at this
  · exact isSkew_conj h2 h1 (by rw [← gram_eq]; exact hx τ) h

theorem theta_mem_dg {ι : Type} [Fintype ι] {r : ℕ} (d : ι → Fin r → ℝ) (hd : ∀ t a, d t a * d t a = 1)
    (Y : WW ι r) (hY : ∀ t, (blk Y t).trace = 0 ∧ IsSkew (dgM (d t)) (blk Y t)) (t : ι) :
    (blk (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) t).trace = 0 ∧
      IsSkew (dgM (d t)) (blk (cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y) t) := by
  rw [blk_cjW]
  refine ⟨by rw [trace_conj (dgM_mul (hd t))]; exact (hY t).1,
    isSkew_conj (dgM_mul (hd t)) (dgM_mul (hd t)) ?_ (hY t).2⟩
  rw [dgM_transpose, cj_dgM, dgM_mul (hd t), Matrix.one_mul]

theorem riemLie_frame_indep_dg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (G : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r) (d e : Ψ → Fin r → ℝ)
    (hd : ∀ t a, d t a * d t a = 1) (he : ∀ t a, e t a * e t a = 1)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = dgM (d τ)) (hy : ∀ τ : Ψ, gram τ.1 G (mat y τ) = dgM (e τ)) :
    riemLie Ψ G x = riemLie Ψ G y := by
  let k : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * mat y τ
  let l : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat y τ)⁻¹ * mat x τ
  have fx := fun τ : Ψ => frame_facts_dg τ.1 G (mat x τ) (d τ) (hd τ) (hx τ)
  have fy := fun τ : Ψ => frame_facts_dg τ.1 G (mat y τ) (e τ) (he τ) (hy τ)
  have hlk : ∀ τ, l τ * k τ = 1 := fun τ => by
    calc l τ * k τ = (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) * mat y τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fx τ).1, Matrix.mul_one, (fy τ).2.1]
  have hkl : ∀ τ, k τ * l τ = 1 := fun τ => by
    calc k τ * l τ = (mat x τ)⁻¹ * (mat y τ * (mat y τ)⁻¹) * mat x τ := by simp only [l, k, Matrix.mul_assoc]
      _ = 1 := by rw [(fy τ).1, Matrix.mul_one, (fx τ).2.1]
  have hK : ∀ τ, (k τ)ᵀ * dgM (d τ) * cj (k τ) = dgM (e τ) := fun τ => by
    have := hy τ
    rw [gram_eq, ← (fx τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [k, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have hL : ∀ τ, (l τ)ᵀ * dgM (e τ) * cj (l τ) = dgM (d τ) := fun τ => by
    have := hx τ
    rw [gram_eq, ← (fy τ).2.2] at this
    refine Eq.trans ?_ this
    simp only [l, Matrix.transpose_mul, cj_mul, Matrix.mul_assoc]
  have m1 := mem_comap_iff_dg G x d hd hx
  have m2 := mem_comap_iff_dg G y e he hy
  have hLV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y), cjW k l Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hlk τ)]; exact ((m2 Y).1 hY τ).1,
        isSkew_conj (hlk τ) (hkl τ) (hK τ) ((m2 Y).1 hY τ).2⟩
  have hKV : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x), cjW l k Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 fun τ => by
      rw [blk_cjW]
      exact ⟨by rw [trace_conj (hkl τ)]; exact ((m1 Y).1 hY τ).1,
        isSkew_conj (hkl τ) (hlk τ) (hL τ) ((m1 Y).1 hY τ).2⟩
  let L : (realLie Ψ G).comap (fromFrame y) ≃ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    LinearEquiv.ofLinear ((cjW k l).restrict hLV) ((cjW l k).restrict hKV)
      (by ext1 Y; exact Subtype.ext (cjW_cjW hkl Y.1)) (by ext1 Y; exact Subtype.ext (cjW_cjW hlk Y.1))
  have hθx : ∀ Y ∈ (realLie Ψ G).comap (fromFrame x),
      cjW (fun t => dgM (d t)) (fun t => dgM (d t)) Y ∈ (realLie Ψ G).comap (fromFrame x) :=
    fun Y hY => (m1 _).2 (theta_mem_dg d hd Y ((m1 Y).1 hY))
  have hθy : ∀ Y ∈ (realLie Ψ G).comap (fromFrame y),
      cjW (fun t => dgM (e t)) (fun t => dgM (e t)) Y ∈ (realLie Ψ G).comap (fromFrame y) :=
    fun Y hY => (m2 _).2 (theta_mem_dg e he Y ((m2 Y).1 hY))
  have hvol : ∀ s, volume (L '' s) = volume s :=
    volume_image_of_form L ((cjW _ _).restrict hθy) ((cjW _ _).restrict hθx)
      (fun Y => Subtype.ext (cjW_cjW (fun t => dgM_mul (he t)) Y.1))
      (fun Y => Subtype.ext (cjW_cjW (fun t => dgM_mul (hd t)) Y.1)) (fun a b => by
        simp only [Submodule.coe_inner, LinearMap.restrict_coe_apply]
        change ⟪cjW (fun t => dgM (d t)) (fun t => dgM (d t)) (cjW k l a.1), cjW k l b.1⟫_ℝ =
          ⟪cjW (fun t => dgM (e t)) (fun t => dgM (e t)) a.1, b.1⟫_ℝ
        rw [inner_theta_dg d hd _ _ (fun t => ((m1 _).1 (hLV _ a.2) t).2),
          inner_theta_dg e he _ _ (fun t => ((m2 _).1 a.2 t).2)]
        simp only [blk_cjW, trace_conj_mul (hlk _)])
  have hLm : Measurable (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) :=
    L.toLinearMap.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) volume = volume := by
    ext s hs
    rw [Measure.map_apply hLm hs, ← hvol, Set.image_preimage_eq s L.surjective]
  have hfx : Measurable (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) :=
    (fromFrame x ∘ₗ ((realLie Ψ G).comap (fromFrame x)).subtype).continuous_of_finiteDimensional.measurable
  have hcomp : (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1) ∘
      (fun Y : (realLie Ψ G).comap (fromFrame y) => L Y) =
      fun Y : (realLie Ψ G).comap (fromFrame y) => fromFrame y Y.1 := by
    funext Y
    funext τ
    change (mat x τ * blk (cjW k l Y.1) τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      mat y τ * blk Y.1 τ * (mat y τ)⁻¹
    rw [blk_cjW]
    calc mat x τ * (k τ * blk Y.1 τ * l τ) * (mat x τ)⁻¹ =
          (mat x τ * (mat x τ)⁻¹) * mat y τ * blk Y.1 τ * (mat y τ)⁻¹ * (mat x τ * (mat x τ)⁻¹) := by
          simp only [k, l, Matrix.mul_assoc]
      _ = _ := by rw [(fx τ).1, Matrix.one_mul, Matrix.mul_one]
  unfold riemLie
  rw [OrthonormalBasis.addHaar_eq_volume, OrthonormalBasis.addHaar_eq_volume, ← hmap,
    Measure.map_map hfx hLm, hcomp]

theorem hermC_neg' {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ (-G) u w = -hermC τ G u w := by
  simp only [hermC, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem gram_neg' {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ (-G) M = -gram τ G M := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Matrix.neg_apply, hermC_neg']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem realSU_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : realSU Ψ (-G) = realSU Ψ G := by
  have key : ∀ (G' : Matrix (Fin r) (Fin r) E) (g : Ψ → GL (Fin r) ℂ), g ∈ realSU Ψ G' ↔
      ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
        hermC τ.1 G' ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) =
          hermC τ.1 G' u w := fun _ _ => Iff.rfl
  ext g
  rw [key, key]
  simp only [hermC_neg', neg_inj]

theorem realLie_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    realLie Ψ (-G) = realLie Ψ G := by
  have key : ∀ (G' : Matrix (Fin r) (Fin r) E) (X : Ψ → Fin r → Fin r → ℂ), X ∈ realLie Ψ G' ↔
      ∀ τ : Ψ, (Matrix.of (X τ)).trace = 0 ∧ ∀ u w,
        hermC τ.1 G' (Matrix.of (X τ) *ᵥ u) w + hermC τ.1 G' u (Matrix.of (X τ) *ᵥ w) = 0 :=
    fun _ _ => Iff.rfl
  ext X
  rw [key, key]
  simp only [hermC_neg', ← neg_add, neg_eq_zero]

theorem riemLie_neg (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) :
    riemLie Ψ (-G) x = riemLie Ψ G x := by
  have key : ∀ S₁ S₂ : Submodule ℝ (Ψ → Fin r → Fin r → ℂ), S₁ = S₂ →
      Measure.map (fun Y : S₁.comap (fromFrame x) => fromFrame x Y.1)
        (stdOrthonormalBasis ℝ (S₁.comap (fromFrame x))).toBasis.addHaar =
      Measure.map (fun Y : S₂.comap (fromFrame x) => fromFrame x Y.1)
        (stdOrthonormalBasis ℝ (S₂.comap (fromFrame x))).toBasis.addHaar := by
    rintro _ _ rfl; rfl
  exact key _ _ (realLie_neg Ψ G)

theorem covolume_congr {Ψ : Finset (E →+* ℂ)} (G₁ G₂ : Matrix (Fin r) (Fin r) E) (x y : Frame Ψ r)
    (Γ : Subgroup (GL (Fin r) E)) (hSU : realSU Ψ G₁ = realSU Ψ G₂) (hν : riemLie Ψ G₁ x = riemLie Ψ G₂ y) :
    covolume (inReal Ψ G₁ Γ) (realSU Ψ G₁) (riemHaar Ψ G₁ x) =
      covolume (inReal Ψ G₂ Γ) (realSU Ψ G₂) (riemHaar Ψ G₂ y) := by
  have key : ∀ (H₁ H₂ : Subgroup (Ψ → GL (Fin r) ℂ)) (_ : H₁ = H₂) [LocallyCompactSpace H₁]
      [LocallyCompactSpace H₂] (ν : Measure (Ψ → Fin r → Fin r → ℂ)),
      @covolume ((Γ.map (embGL Ψ r)).subgroupOf H₁) H₁ _ _ (borel H₁)
        (@tangentHaar _ _ H₁ _ (borel H₁) (@BorelSpace.mk H₁ _ (borel H₁) rfl) ν) =
      @covolume ((Γ.map (embGL Ψ r)).subgroupOf H₂) H₂ _ _ (borel H₂)
        (@tangentHaar _ _ H₂ _ (borel H₂) (@BorelSpace.mk H₂ _ (borel H₂) rfl) ν) := by
    intro H₁ H₂ h _ _ ν
    subst h
    rfl
  unfold riemHaar
  rw [hν]
  exact key _ _ hSU _

theorem covolume_neg_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ)) (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 : Ψ → ℕ) (p1 : ℕ) (Γ : Subgroup (GL (Fin r) E)), Ψ' = Ψ → G' = -G → (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  intro E _ _ _ r Ψ Ψ' G G' x x' p0 p1 Γ hΨ hG _ hx hx'
  subst hΨ hG
  refine covolume_congr G (-G) x x' Γ (realSU_neg _ G).symm ?_
  rw [riemLie_neg]
  refine riemLie_frame_indep_dg G x x' (fun τ a => sgn (p0 τ) (a : ℕ)) (fun _ a => -sgn p1 (a : ℕ))
    (fun τ a => sgn_sq _ _) (fun _ a => by rw [neg_mul_neg, sgn_sq]) hx (fun τ => ?_)
  have h := hx' τ
  rw [gram_neg'] at h
  rw [← neg_neg (gram _ G _), h]
  ext a b
  by_cases hab : a = b <;> simp [hab, Matrix.diagonal_apply]

end GlobalTheory.CovolNegFrame
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_frame_congruence_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ)) (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 : Ψ → ℕ) (p1 : ℕ) (Γ : Subgroup (GL (Fin r) E)), Ψ' = Ψ → G' = -G → (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  atlas_forward_decl GlobalTheory.CovolNegFrame.covolume_neg_frame
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_measure_finite_part_preimage : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  first | exact @GlobalTheory.CovTop.VolPush.meas_translate_eq | exact GlobalTheory.CovTop.VolPush.meas_translate_eq | (intros; apply GlobalTheory.CovTop.VolPush.meas_translate_eq <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_frame_real_special_unitary : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (x₀ : Frame Ψ V.rank) (σ : D.what₂.Tau ≃ Ψ) (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank) (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (J : Type) (s : J → Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V) (F : J → Set (realSU Ψ Gm)) (ρ₀ : D.what₂.Tau), Gm = -(V.gram)ᵀ → IsInfFam θ → IsRealPart V θ A rp → IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) Ψ Gm x₀ σ A e → (∀ ρ, (σ ρ).1 = tauE D ρ) → (∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b) → (∀ j, ∀ γ ∈ inReal Ψ Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)), ∀ y ∈ F j, γ * y ∈ F j → γ = 1) → (∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧ ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j')) → (∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V → matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → finE V ((h j)⁻¹ * g * h j) ∈ K → γ ∈ ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)) → ∀ g ∈ GQ V, ∀ (j j' : J) (y : GA D V), (finE V ((h j)⁻¹ * y) ∈ K ∧ π (rp y) ∈ F j ∧ 0 < (UpqT.mat (rp y ρ₀)).det.im) → (finE V ((h j')⁻¹ * (g * y)) ∈ K ∧ π (rp (g * y)) ∈ F j' ∧ 0 < (UpqT.mat (rp (g * y) ρ₀)).det.im) → UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det = UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp (g * y) ρ₀)).det → g = 1 ∧ j = j' := by
  first | exact @GlobalTheory.TubePack.tube_disjoint | exact GlobalTheory.TubePack.tube_disjoint | (intros; apply GlobalTheory.TubePack.tube_disjoint <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.MassBridge

theorem core (D : D7) (V : HSp D) (r : ℕ) (hrk : V.rank = r) (hV : V.SigOK) (P Q : ℕ)
    (hsig : ∀ τ, V.sig τ = (P, Q)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (hKo : IsOpen {h : GA D V | finE V h ∈ K}) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hF : IsMeasFD V K μ 𝓕) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ))
    (x : Frame Ψ r) (p0 : Ψ → ℕ) (J : Type)
    (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V)
    (hr : 2 ≤ r)
    (hx : ∀ τ : Ψ, gram τ.1 (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (hΨ : ∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = tauE D ρ)
    (hh : ∀ j, h j ∈ GfC V)
    (h4 : ∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧
        ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j'))
    (h5 : ∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (γr : GL (Fin r) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm) =
        (γr : Matrix (Fin r) (Fin r) D.host.E) → (γr : Matrix (Fin r) (Fin r) D.host.E).det = 1 →
      finE V ((h j)⁻¹ * g * h j) ∈ K →
      γr ∈ ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (Λ : Set (Fin r → D.host.E)) (s j)) :
    ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * r ^ 2)) * ∑' j, covolume
      (inReal Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
          (Λ : Set (Fin r → D.host.E)) (s j)))
      (realSU Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))))
      (riemHaar Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) x) ≤ μ 𝓕 := by
  subst hrk
  classical
  change ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * V.rank ^ 2)) * ∑' j, covolume
      (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ μ 𝓕
  have hx' : ∀ τ : Ψ, gram τ.1 (V.gram)ᵀ (mat x τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := hx
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨X₀, σ, x₀, e, hG, hσ, hx₀, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 :=
    fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ hid
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ D.R.f := UpperTheory.Mu.one_le_f D.R
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  obtain ⟨eΨ, heΨ⟩ := hΨ
  have hΨX : X₀.Ψ = Ψ := by
    ext τ; constructor
    · intro hτ
      obtain ⟨ρ, hρ⟩ := σ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← hσ ρ, hρ]
      rw [e1, ← heΨ ρ]; exact (eΨ ρ).2
    · intro hτ
      obtain ⟨ρ, hρ⟩ := eΨ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← heΨ ρ, hρ]
      rw [e1, ← hσ ρ]; exact (σ ρ).2
  have hherm : ∀ a b, cc ((V.gram)ᵀ a b) = (V.gram)ᵀ b a := by
    intro a b
    have e1 := X₀.Gm_herm a b
    rw [hG] at e1
    simp only [cc, Matrix.neg_apply, Matrix.transpose_apply, map_neg, neg_inj] at e1 ⊢
    exact e1
  have htr : ∀ j, covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) =
      covolume (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀) := fun j =>
    GlobalTheory.T.gram_frame_congruence_subgroup D.host.E V.rank Ψ X₀.Ψ (V.gram)ᵀ X₀.Gm x x₀ p0 X₀.p0 _ hΨX hG hherm hx' hx₀
  choose F hFm hFcov hFfree using fun j => GlobalTheory.T.exists_packingSet_measure_ge_covolume (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀)
    (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j))) (GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary _ _ _ _ _)
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  let B : J → Set (∀ ρ, Upq V ρ) := fun j => π ⁻¹' F j ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    (hπc.measurable (hFm j)).inter (GlobalTheory.T.measurableSet_det_im_pos_at_index D.what₂.Tau _ _ ρ₀)
  let T : J → Set (GA D V) := fun j => {y | finE V ((h j)⁻¹ * y) ∈ K ∧ rp y ∈ B j}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    ((hKo.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm j))
  have hμT : ∀ j, μ (T j) = Measure.pi m (B j) := fun j =>
    GlobalTheory.T.level_measure_finite_part_preimage D V θ A m rp K μ hV hθ hA hm hrpc hrp hKo hF.1 (h j) (hh j) (B j) (hBm j)
  have hlow : ∀ j, ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) ≤ μ (T j) := by
    intro j
    rw [hμT j]
    exact GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ π m ρ₀ (by omega) hid hπc hπ hπe hm (F j) (hFm j)
  have hdisj := GlobalTheory.T.indefinite_frame_real_special_unitary D V θ A rp X₀.Ψ X₀.Gm x₀ σ e π K Λ J s h F ρ₀ hG hθ hrp hid hσ hπe hFfree h4
    (fun j g γ hg hmg hd hK => h5 j g γ γ hg hmg rfl hd hK)
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
  refine iSup_le fun J0 => ?_
  let sc : GA D V → ℕ := fun y => UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det
  have hscm : Measurable sc := by
    have hc : Continuous fun g : Upq V ρ₀ => (UpqT.mat g).det := (continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat
    exact (UpperTheory.Ram.Sector.measurable_sec _).comp
      (hc.measurable.comp ((measurable_pi_apply ρ₀).comp hrpc.measurable))
  have hlay : ∀ k, ∑ j ∈ J0, μ (T j ∩ {y | sc y = k}) ≤ μ 𝓕 := by
    intro k
    let Tk : J → Set (GA D V) := fun j => T j ∩ {y | sc y = k}
    have hTkm : ∀ j, MeasurableSet (Tk j) := fun j => (hTm j).inter (hscm (measurableSet_singleton k))
    let S := ⋃ j ∈ J0, Tk j
    have hSm : MeasurableSet S := Finset.measurableSet_biUnion J0 fun j _ => hTkm j
    have hTd : Set.PairwiseDisjoint (↑J0) Tk := by
      intro j _ j' _ hne
      refine Set.disjoint_left.2 fun y hy hy' => hne ?_
      exact (hdisj 1 (GQ V).one_mem j j' y hy.1 (by rw [one_mul]; exact hy'.1) (by rw [one_mul])).2
    have hμS : μ S = ∑ j ∈ J0, μ (Tk j) := measure_biUnion_finset hTd fun j _ => hTkm j
    have hSF : μ S ≤ μ 𝓕 := by
      refine hF.2.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet ?_
      intro g g' hne
      refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hz' => hne ?_)
      obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz.1
      obtain ⟨y', hy', hyz'⟩ := Set.mem_smul_set.1 hz'.1
      obtain ⟨j, -, hyj⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨j', -, hyj'⟩ := Set.mem_iUnion₂.1 hy'
      have h1 : (g : GA D V) * y = z := hyz
      have h2 : (g' : GA D V) * y' = z := hyz'
      have e1 : ((g'⁻¹ * g : GQ V) : GA D V) * y = y' := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h1, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
      have e2 := (hdisj _ (g'⁻¹ * g).2 j j' y hyj.1 (by rw [e1]; exact hyj'.1)
        (by rw [e1]; exact (hyj.2 : sc y = k).trans (hyj'.2 : sc y' = k).symm)).1
      have e3 : g'⁻¹ * g = 1 := Subtype.ext e2
      exact (inv_mul_eq_one.1 e3).symm
    exact hμS ▸ hSF
  have hw : NumberField.Units.torsionOrder D.host.E ≤ 2 ^ (D.R.f * V.rank ^ 2) :=
    (UpperTheory.Mu.host_torsionOrder_le D.host).trans (UpperTheory.Ram.Sector.eight_sq_le hf (by omega))
  refine UpperTheory.Ram.Sector.le_of_mul_le hw ?_
  rw [Finset.mul_sum]
  calc ∑ j ∈ J0, ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
        covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
          (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ ∑ j ∈ J0, μ (T j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [htr j, ← hcard]
        calc _ ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) := by
              gcongr; exact hFcov j
          _ ≤ μ (T j) := hlow j
    _ ≤ _ := UpperTheory.Ram.Sector.sum_le_of_layers μ T sc _
        (fun y => UpperTheory.Ram.Sector.sec_lt (NumberField.Units.torsionOrder_pos D.host.E) _) J0 _ hlay

end GlobalTheory.CovTop.MassBridge

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MassBridge

theorem bridge_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) → (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) → (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  refine ⟨1 / 32, by norm_num, by norm_num, ?_⟩
  intro D Tu Cl t0 hCl i μ 𝓕 hF G Λ Ψ x p0 J s h hdata hlink
  obtain ⟨hr, -, -, -, hx, -, -⟩ := hdata
  obtain ⟨hG, hΨ, hh, h4, h5⟩ := hlink
  subst hG
  exact core D (Wc D i) D.R.r (rank_Wc i) (D.sp.W_sig _) _ _ (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) _
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _) μ 𝓕 hF Λ Ψ x p0 J s h hr hx hΨ hh h4 h5

end GlobalTheory.CovTop.MassBridge
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MassBridge

theorem mass_bridge : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), 2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f ∧ (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  obtain ⟨c, hc0, hc1, hB⟩ := bridge_bound
  refine ⟨c, hc0, hc1, fun D Tu Cl t0 hCl i μ 𝓕 hμ => ?_⟩
  obtain ⟨G, Λ, Ψ, x, p0, J, s, h, hF, hL⟩ := GlobalTheory.MassLink.data_link D Tu Cl t0 hCl i
  exact ⟨G, Λ, Ψ, x, p0, J, s, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.1, hF.2.2.2.2.2.2,
    hB D Tu Cl t0 hCl i μ 𝓕 hμ G Λ Ψ x p0 J s h hF hL⟩

end GlobalTheory.CovTop.MassBridge
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_level_self_dual_lattice : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), 2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f ∧ (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  atlas_forward_decl GlobalTheory.CovTop.MassBridge.mass_bridge
end
