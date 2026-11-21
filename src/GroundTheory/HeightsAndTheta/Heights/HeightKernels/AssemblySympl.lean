import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplOrbit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinkowskiBox
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplMinBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceMem
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReducePosDef
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplReduceConj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplDetSchur

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplecticReduction.proof (hStep : SymplStep.Statement) (hDet : SymplDetBound.Statement) :
    SymplecticReduction.Statement := by
  intro g _ G hG hpos
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne g)
  obtain ⟨ρsq, hleast, hρ, hle, P, hP, hent, hdet⟩ :=
    hStep n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => hDet n H hH hHpos)
  refine ⟨ρsq, hleast, ?_, P, hP, hent, ?_⟩
  · push_cast; linarith
  · calc (symplGram P G).toBlocks₁₁.det ≤ ρsq * (2 * (n : ℝ)) ^ n := hdet
      _ ≤ ρsq * (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        apply mul_le_mul_of_nonneg_left _ hρ.le
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplOmegaMem

theorem mul_J_mul_transpose_apply {R : Type*} [CommRing R] {l : Type*} [Fintype l]
    [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) R) (x y : l ⊕ l) :
    (M * J l R * Mᵀ) x y = symplOmega (M x) (M y) := by
  rw [symplOmega, dotProduct_mulVec, Matrix.mul_apply]
  rfl

end PSymplOmegaMem

theorem SymplOmegaMem.proof : SymplOmegaMem.Statement := by
  intro R _ l _ _ M
  rw [SymplecticGroup.mem_iff]
  constructor
  · intro h x y
    rw [← PSymplOmegaMem.mul_J_mul_transpose_apply, h]
  · intro h
    ext x y
    rw [PSymplOmegaMem.mul_J_mul_transpose_apply, h]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplCons

theorem J_mulVec_inl {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inl i) = -v (Sum.inr i) := by
  simp [Matrix.J, fromBlocks_mulVec, neg_mulVec]

theorem J_mulVec_inr {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (v : l ⊕ l → R) (i : l) : (J l R *ᵥ v) (Sum.inr i) = v (Sum.inl i) := by
  simp [Matrix.J, fromBlocks_mulVec]

theorem symplOmega_eq_sum {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) :
    symplOmega u v = ∑ i, (u (Sum.inr i) * v (Sum.inl i) - u (Sum.inl i) * v (Sum.inr i)) := by
  unfold symplOmega dotProduct
  rw [Fintype.sum_sum_type]
  simp only [J_mulVec_inl, J_mulVec_inr, mul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_sub_distrib]
  ring

end PSymplCons

open PSymplCons in

theorem SymplCons.proof : SymplCons.Statement := by
  intro R _ n
  refine ⟨fun u => ?_, fun p q p' q' w w' => ?_⟩
  · funext x
    rcases x with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [symplCons, symplTail]
  · rw [symplOmega_eq_sum, symplOmega_eq_sum, Fin.sum_univ_succ]
    simp [symplCons]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplExtMem

lemma omega_zero_left {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega (0 : l ⊕ l → R) w = 0 := by
  simp [symplOmega]

lemma omega_zero_right {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega w (0 : l ⊕ l → R) = 0 := by
  simp [symplOmega]

variable {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

lemma row_e : symplExt α β γ δ Q (Sum.inl 0) = symplCons α β 0 := rfl

lemma row_f : symplExt α β γ δ Q (Sum.inr 0) = symplCons γ δ 0 := rfl

lemma row_inl (i : Fin n) :
    symplExt α β γ δ Q (Sum.inl i.succ) = symplCons 0 0 (Q (Sum.inl i)) := rfl

lemma row_inr (i : Fin n) :
    symplExt α β γ δ Q (Sum.inr i.succ) = symplCons 0 0 (Q (Sum.inr i)) := rfl

end PSymplExtMem

open PSymplExtMem in

theorem SymplExtMem.proof (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplExtMem.Statement := by
  intro R _ n α β γ δ Q hdet hQ
  rw [h1 R (Fin (n + 1))]
  have hQ' := (h1 R (Fin n) Q).1 hQ
  have hc := (h2 R n).2
  rintro (x | x) (y | y) <;> cases x using Fin.cases <;> cases y using Fin.cases <;>
    simp only [row_e, row_f, row_inl, row_inr, hc, hQ', omega_zero_left, omega_zero_right] <;>
    simp [Matrix.J, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj] <;>
    first
      | ring1
      | linear_combination hdet
      | linear_combination (-1 : R) * hdet
      | exact fun h => absurd (Eq.symm h) (Fin.succ_ne_zero _)

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplExtVecMul.proof : SymplExtVecMul.Statement := by
  intro R _ n α β γ δ p q Q w
  funext y
  rcases y with y | y <;> refine Fin.cases ?_ (fun j => ?_) y <;>
    simp [vecMul, dotProduct, symplCons, symplExt, Fintype.sum_sum_type, Fin.sum_univ_succ]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplTwoRow

def twoBlock (n : ℕ) (a b r s : ℤ) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℤ :=
  Matrix.of (vecCons (vecCons a (vecCons b 0))
    (vecCons (vecCons (-s) (vecCons r 0)) fun k => vecCons 0 (vecCons 0 (Pi.single k 1))))

theorem twoBlock_mul_transpose {n : ℕ} {c d x y : ℤ} (h : x * c + y * d = 1) :
    twoBlock n c d x y * (twoBlock n x y c d)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
  simp [twoBlock, Fin.sum_univ_succ, Matrix.one_apply, Pi.single_apply] <;>
  first | linarith | (split_ifs <;> simp_all [Fin.ext_iff]) | simp [Fin.ext_iff]

end PSymplTwoRow

open PSymplTwoRow in

theorem SymplTwoRow.proof : SymplTwoRow.Statement := by
  intro n c d x y h
  refine ⟨fromBlocks (twoBlock n c d x y) 0 0 (twoBlock n x y c d), ?_, ?_⟩
  · rw [SymplecticGroup.mem_iff]
    have h1 := twoBlock_mul_transpose (n := n) h
    have h2 : twoBlock n x y c d * (twoBlock n c d x y)ᵀ = 1 := by
      rw [← transpose_transpose (twoBlock n x y c d), ← transpose_mul, h1, transpose_one]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, h1, h2]
  · funext z
    rcases z with i | i
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons, twoBlock]
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
        simp [symplCons]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PSymplGcd

theorem of_gcd_ne_zero (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  refine ⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩
  have h := Int.gcd_eq_gcd_ab a b
  apply mul_left_cancel₀ hc
  linear_combination (-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h

end PSymplGcd

theorem SymplGcd.proof : SymplGcd.Statement := by
  intro a b
  by_cases hc : (Int.gcd a b : ℤ) = 0
  · have h0 : Int.gcd a b = 0 := by exact_mod_cast hc
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    exact ⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩
  · exact PSymplGcd.of_gcd_ne_zero a b hc

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplQuadDiag

theorem abs_det_eq_one_of_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (h : Oᵀ * O = 1) : |O.det| = 1 := by
  have h1 : O.det * O.det = 1 := by
    have := congrArg Matrix.det h
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |O.det| * |O.det| = 1 := by rw [← abs_mul, h1, abs_one]
  nlinarith [abs_nonneg O.det]

end PSymplQuadDiag

theorem SymplQuadDiag.proof : SymplQuadDiag.Statement := by
  intro ι _ _ G hG
  have hH := hG.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [hUdef]
  refine ⟨star U, hH.eigenvalues, fun i => hG.eigenvalues_pos i, ?_, ?_, ?_⟩
  · rw [hstar]
    apply PSymplQuadDiag.abs_det_eq_one_of_mul_transpose
    rw [transpose_transpose, ← hstar]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · rw [hH.det_eq_prod_eigenvalues]
    simp
  · intro x
    have hx : x ᵥ* U = star U *ᵥ x := by rw [hstar, mulVec_transpose]
    calc qf G x = x ⬝ᵥ (U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x))) := by
          have hG' : G *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
            rw [mulVec_mulVec, mulVec_mulVec, ← hspec]
          rw [qf, hG']
      _ = (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
          rw [dotProduct_mulVec, hx]
      _ = ∑ i, hH.eigenvalues i * (star U *ᵥ x) i ^ 2 := by
          simp only [dotProduct, mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
            id]
          exact Finset.sum_congr rfl fun i _ => by ring

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplBoxVolume

theorem set_eq_preimage {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      (Matrix.toLin' A) ⁻¹' (Set.pi Set.univ fun i => Set.Ioo (-a i) (a i)) := by
  ext x
  simp [abs_lt]

end PSymplBoxVolume

open PSymplBoxVolume in

theorem SymplBoxVolume.proof : SymplBoxVolume.Statement := by
  intro ι _ _ A a hA ha
  rw [set_eq_preimage, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin'])
    , Real.volume_pi_Ioo, LinearMap.det_toLin',
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [ha i]),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, div_eq_mul_inv, mul_comm]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplShortPrim

lemma intVec_smul {ι : Type} (m : ℤ) (w : ι → ℤ) : intVec (m • w) = (m : ℝ) • intVec w := by
  funext i
  simp [intVec]

lemma qf_smul {ι : Type} [Fintype ι] (Y : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    qf Y (c • x) = c ^ 2 * qf Y x := by
  simp only [qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

end PSymplShortPrim

open PSymplShortPrim in

theorem SymplShortPrim.proof : SymplShortPrim.Statement := by
  intro ι _ _ G hG v w m hvw hv hmin
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by simp [hvw])
  have hwR : intVec w ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa [intVec] using this
  have hq : 0 < qf G (intVec w) := by
    have := hG.dotProduct_mulVec_pos hwR
    simpa [qf] using this
  have hle := hmin w hw
  rw [hvw, intVec_smul, qf_smul] at hle
  have hm2 : ((m : ℝ)) ^ 2 ≤ 1 := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hm2' : m ^ 2 ≤ 1 := by exact_mod_cast hm2
  have habs : |m| ≤ 1 := (sq_le_one_iff_abs_le_one m).mp hm2'
  rw [abs_le] at habs
  omega

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplGramMem

lemma det_map_cast {n : ℕ} {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hP : P ∈ symplecticGroup (Fin n) ℤ) : (P.map (Int.cast : ℤ → ℝ)).det = 1 := by
  have h := SymplecticGroup.det_eq_one (SymplecticGroup.map_mem hP (Int.castRingHom ℝ))
  simpa using h

lemma gram_diag {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) (x : l) :
    symplGram P G x x = qf G (intVec (P x)) := by
  unfold symplGram qf intVec
  rw [Matrix.mul_mul_apply]
  rfl

end PSymplGramMem

open PSymplGramMem in

theorem SymplGramMem.proof : SymplGramMem.Statement := by
  intro n P G hP hG hGpd
  set P' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := P.map (Int.cast : ℤ → ℝ) with hP'
  have hP'mem : P' ∈ symplecticGroup (Fin n) ℝ := SymplecticGroup.map_mem hP (Int.castRingHom ℝ)
  refine ⟨?_, ?_, ?_, fun x => gram_diag P G x⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hP'mem hG) (SymplecticGroup.transpose_mem hP'mem)
  · have hdet : IsUnit P'.det := by rw [det_map_cast hP]; exact isUnit_one
    have hinj : Function.Injective P'.vecMul :=
      vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    have h := hGpd.mul_mul_conjTranspose_same hinj
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  · intro Q
    unfold symplGram
    have hmap : (Q * P).map (Int.cast : ℤ → ℝ) = Q.map (Int.cast : ℤ → ℝ) * P.map (Int.cast : ℤ → ℝ) :=
      Matrix.map_mul (f := Int.castRingHom ℝ)
    rw [hmap, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplReduceStep

theorem symplExt_map {n : ℕ} (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) :
    (symplExt (1 : ℤ) 0 0 1 Q).map (Int.cast : ℤ → ℝ) =
      symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) := by
  ext x y
  rcases x with i | i <;> rcases y with j | j <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [symplExt, symplCons]

theorem schur_toBlocks {n : ℕ} (K : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    (Matrix.of fun i j : Fin n => K.toBlocks₁₁ i.succ j.succ -
        K.toBlocks₁₁ i.succ 0 * K.toBlocks₁₁ 0 j.succ / K.toBlocks₁₁ 0 0) =
      (symplReduce K).toBlocks₁₁ := by
  ext i j
  simp [symplReduce, Matrix.toBlocks₁₁]

end PSymplReduceStep

theorem SymplReduceStep.proof (h1 : SymplExtMem.Statement) (h2 : SymplReduceConj.Statement)
    (h3 : SymplDetSchur.Statement) : SymplReduceStep.Statement := by
  intro n H Q hH hQ
  refine ⟨symplExt 1 0 0 1 Q, h1 ℤ n 1 0 0 1 Q (by norm_num) hQ, ?_⟩
  obtain ⟨he, hred⟩ := h2 n H (Q.map (Int.cast : ℤ → ℝ))
  rw [symplGram, PSymplReduceStep.symplExt_map]
  generalize symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)) * H *
    (symplExt 1 0 0 1 (Q.map (Int.cast : ℤ → ℝ)))ᵀ = K at he hred ⊢
  refine ⟨he, ?_⟩
  have hk0 : K.toBlocks₁₁ 0 0 = H (Sum.inl 0) (Sum.inl 0) := he
  rw [h3 n K.toBlocks₁₁ (hk0 ▸ hH), PSymplReduceStep.schur_toBlocks, hred, hk0]
  rfl

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplDetBound

theorem step_bound (n : ℕ) (ρ : ℝ) (hle : ρ ≤ 2 * ((n : ℝ) + 1)) :
    ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have h0 : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ n := by positivity
  calc ρ * (2 * (n : ℝ)) ^ n ≤ (2 * ((n : ℝ) + 1)) * (2 * (n : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hle h0
    _ ≤ (2 * ((n : ℝ) + 1)) * (2 * ((n : ℝ) + 1)) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith
    _ = (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
        push_cast; ring

end PSymplDetBound

theorem SymplDetBound.proof (h1 : SymplStep.Statement) : SymplDetBound.Statement := by
  intro n
  induction n with
  | zero =>
    intro G _ _
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    rw [Matrix.det_isEmpty]
    simp
  | succ n ih =>
    intro G hG hpos
    obtain ⟨ρsq, _, _, hle, P, hP, _, hdet⟩ :=
      h1 n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => ih H hH hHpos)
    exact ⟨P, hP, hdet.trans (PSymplDetBound.step_bound n ρsq hle)⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SymplOmegaMem.full : SymplOmegaMem.Statement :=
  SymplOmegaMem.proof

theorem SymplCons.full : SymplCons.Statement :=
  SymplCons.proof

theorem SymplExtVecMul.full : SymplExtVecMul.Statement :=
  SymplExtVecMul.proof

theorem SymplTwoRow.full : SymplTwoRow.Statement :=
  SymplTwoRow.proof

theorem SymplGcd.full : SymplGcd.Statement :=
  SymplGcd.proof

theorem SymplQuadDiag.full : SymplQuadDiag.Statement :=
  SymplQuadDiag.proof

theorem SymplBoxVolume.full : SymplBoxVolume.Statement :=
  SymplBoxVolume.proof

theorem SymplShortPrim.full : SymplShortPrim.Statement :=
  SymplShortPrim.proof

theorem SymplGramMem.full : SymplGramMem.Statement :=
  SymplGramMem.proof

theorem SymplReducePosDef.full : SymplReducePosDef.Statement :=
  SymplReducePosDef.proof

theorem SymplReduceConj.full : SymplReduceConj.Statement :=
  SymplReduceConj.proof

theorem SymplDetSchur.full : SymplDetSchur.Statement :=
  SymplDetSchur.proof

theorem SymplExtMem.full : SymplExtMem.Statement :=
  SymplExtMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplMinkowskiBox.full : SymplMinkowskiBox.Statement :=
  SymplMinkowskiBox.proof SymplBoxVolume.full

theorem SymplMinExists.full : SymplMinExists.Statement :=
  SymplMinExists.proof SymplQuadDiag.full

theorem SymplReduceMem.full : SymplReduceMem.Statement :=
  SymplReduceMem.proof SymplOmegaMem.full SymplCons.full

theorem SymplOrbit.full : SymplOrbit.Statement :=
  SymplOrbit.proof SymplExtMem.full SymplExtVecMul.full SymplTwoRow.full SymplGcd.full SymplCons.full

theorem SymplMinBound.full : SymplMinBound.Statement :=
  SymplMinBound.proof SymplQuadDiag.full SymplMinkowskiBox.full

theorem SymplReduceStep.full : SymplReduceStep.Statement :=
  SymplReduceStep.proof SymplExtMem.full SymplReduceConj.full SymplDetSchur.full

theorem SymplFirstRow.full : SymplFirstRow.Statement :=
  SymplFirstRow.proof SymplMinExists.full SymplMinBound.full SymplOrbit.full SymplShortPrim.full SymplGramMem.full

theorem SymplStep.full : SymplStep.Statement :=
  SymplStep.proof SymplFirstRow.full SymplGramMem.full SymplReduceMem.full SymplReducePosDef.full SymplReduceStep.full

theorem SymplDetBound.full : SymplDetBound.Statement :=
  SymplDetBound.proof SymplStep.full

theorem SymplecticReduction.full : SymplecticReduction.Statement :=
  SymplecticReduction.proof SymplStep.full SymplDetBound.full

end GroundTheory.Heights₂.Heights
end
