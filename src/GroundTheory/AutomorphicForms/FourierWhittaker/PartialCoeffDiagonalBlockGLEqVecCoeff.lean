import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.AdelicCharPairTorusPtSingle
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice

section
open Matrix

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

variable {n : ℕ} {R : Type*} [CommRing R]

def uN (X : Pos n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => if h : a < b then X ⟨(a, b), h⟩ else 0

theorem uN_apply (X : Pos n → R) (a b : Fin n) :
    uN X a b = if h : a < b then X ⟨(a, b), h⟩ else 0 := rfl

theorem uN_add (X Y : Pos n → R) : uN (X + Y) = uN X + uN Y := by
  ext a b; simp only [uN_apply, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp

theorem uN_zero : uN (0 : Pos n → R) = 0 := by
  ext a b; simp only [uN_apply, Pi.zero_apply, Matrix.zero_apply]; split_ifs <;> rfl


def uMat (X : Pos n → R) : Matrix (Fin n) (Fin n) R := 1 + uN X

theorem uMat_apply (X : Pos n → R) (a b : Fin n) :
    uMat X a b = if a = b then 1 else if h : a < b then X ⟨(a, b), h⟩ else 0 := by
  simp only [uMat, Matrix.add_apply, Matrix.one_apply, uN_apply]
  by_cases h1 : a = b
  · subst h1; simp
  · rw [if_neg h1, if_neg h1, zero_add]

theorem uMat_zero : uMat (0 : Pos n → R) = 1 := by simp [uMat, uN_zero]

theorem det_uMat (X : Pos n → R) : (uMat X).det = 1 := by
  have hT : (uMat X).IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    rw [uMat_apply, if_neg (ne_of_gt hab'), dif_neg (not_lt.2 hab'.le)]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [uMat_apply, if_pos rfl]

def uGL (X : Pos n → R) : GL (Fin n) R :=
  ((Matrix.isUnit_iff_isUnit_det (uMat X)).2 (by rw [det_uMat]; exact isUnit_one)).unit

@[simp] theorem coe_uGL (X : Pos n → R) : ((uGL X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = uMat X :=
  rfl

theorem uGL_zero : uGL (0 : Pos n → R) = 1 := Units.ext (by simp [uMat_zero])

theorem map_uMat {S : Type*} [CommRing S] (f : R →+* S) (X : Pos n → R) :
    (uMat X).map f = uMat (fun p => f (X p)) := by
  ext a b
  simp only [Matrix.map_apply, uMat_apply]
  split_ifs <;> simp

def colX (k : ℕ) (x : Fin k → R) : Pos n → R :=
  fun p => if h : p.1.2.val = k then x ⟨p.1.1.val, by have := p.2; rw [Fin.lt_def] at this; omega⟩
    else 0

theorem colX_apply (k : ℕ) (x : Fin k → R) (p : Pos n) :
    colX k x p = if h : p.1.2.val = k then
      x ⟨p.1.1.val, by have := p.2; rw [Fin.lt_def] at this; omega⟩ else 0 := rfl

theorem colX_add (k : ℕ) (x y : Fin k → R) : colX (n := n) k (x + y) = colX k x + colX k y := by
  funext p; simp only [colX_apply, Pi.add_apply]; split_ifs <;> simp

theorem colX_zero (k : ℕ) : colX (n := n) k (0 : Fin k → R) = 0 := by
  funext p; simp only [colX_apply, Pi.zero_apply]; split_ifs <;> rfl


theorem uN_mul_uN_colX {k : ℕ} {Y : Pos n → R} (hY : ∀ p : Pos n, p.1.2.val ≤ k → Y p = 0)
    (x : Fin k → R) : uN Y * uN (colX k x) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [uN_apply, uN_apply]
  by_cases hcb : c < b
  · rw [dif_pos hcb, colX_apply]
    by_cases hb : b.val = k
    · rw [dif_pos hb]
      by_cases hac : a < c
      · rw [dif_pos hac, hY _ (by rw [Fin.lt_def] at hcb; simp only; omega), zero_mul]
      · rw [dif_neg hac, zero_mul]
    · rw [dif_neg hb, mul_zero]
  · rw [dif_neg hcb, mul_zero]

theorem uMat_mul_uMat_colX {k : ℕ} {Y : Pos n → R} (hY : ∀ p : Pos n, p.1.2.val ≤ k → Y p = 0)
    (x : Fin k → R) : uMat Y * uMat (colX k x) = uMat (Y + colX k x) := by
  rw [uMat, uMat, uMat, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul,
    uN_mul_uN_colX hY, add_zero, uN_add, add_assoc]

def colGL (k : ℕ) (x : Fin k → R) : GL (Fin n) R := uGL (colX k x)

theorem colX_le (k : ℕ) (x : Fin k → R) (p : Pos n) (hp : p.1.2.val ≤ k - 1 ∨ k < p.1.2.val) :
    colX k x p = 0 := by
  rw [colX_apply, dif_neg]
  intro h
  rcases hp with hp | hp
  · have := p.2; rw [Fin.lt_def] at this; omega
  · omega

theorem uN_colX_mul_uN_colX (k : ℕ) (x y : Fin k → R) :
    uN (colX (n := n) k x) * uN (colX k y) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [uN_apply, colX_apply]
  split_ifs with h1 h2 h3 h4 <;> first | simp | (rw [Fin.lt_def] at h3; omega)

theorem colGL_add (k : ℕ) (x y : Fin k → R) :
    colGL (n := n) k (x + y) = colGL k x * colGL k y := by
  refine Units.ext ?_
  simp only [colGL, Units.val_mul, coe_uGL, uMat, colX_add, uN_add, mul_add, add_mul, one_mul,
    mul_one, uN_colX_mul_uN_colX, add_zero, add_assoc]

theorem colGL_zero (k : ℕ) : colGL (n := n) (R := R) k 0 = 1 := by
  rw [colGL, colX_zero, uGL_zero]

theorem colGL_neg (k : ℕ) (x : Fin k → R) : colGL (n := n) k (-x) = (colGL k x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← colGL_add, neg_add_cancel, colGL_zero]

theorem map_colGL {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (x : Fin k → R) :
    ((colGL (n := n) k x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f =
      (colGL (n := n) k (fun i => f (x i)) : GL (Fin n) S) := by
  rw [colGL, colGL, coe_uGL, coe_uGL, map_uMat]
  congr 1
  funext p
  simp only [colX_apply]
  split_ifs <;> simp

section Block

variable {j : ℕ}

def splitIdx (hj : j ≤ n) : Fin n ≃ Fin j ⊕ Fin (n - j) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

theorem splitIdx_of_lt (hj : j ≤ n) (a : Fin n) (ha : a.val < j) :
    splitIdx hj a = Sum.inl ⟨a.val, ha⟩ := by
  have : finCongr (by omega : n = j + (n - j)) a = Fin.castAdd (n - j) ⟨a.val, ha⟩ := Fin.ext rfl
  rw [splitIdx, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]

theorem splitIdx_of_ge (hj : j ≤ n) (a : Fin n) (ha : j ≤ a.val) :
    splitIdx hj a = Sum.inr ⟨a.val - j, by omega⟩ := by
  have : finCongr (by omega : n = j + (n - j)) a = Fin.natAdd j ⟨a.val - j, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [splitIdx, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]

def blockMat (hj : j ≤ n) (h : Matrix (Fin j) (Fin j) R) : Matrix (Fin n) (Fin n) R :=
  (Matrix.fromBlocks h 0 0 1).submatrix (splitIdx hj) (splitIdx hj)

theorem blockMat_apply (hj : j ≤ n) (h : Matrix (Fin j) (Fin j) R) (a b : Fin n) :
    blockMat hj h a b = if ha : a.val < j then (if hb : b.val < j then h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      else 0) else (if a = b then 1 else 0) := by
  rw [blockMat, Matrix.submatrix_apply]
  by_cases ha : a.val < j
  · rw [splitIdx_of_lt hj a ha, dif_pos ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj b hb, dif_pos hb, Matrix.fromBlocks_apply₁₁]
    · rw [splitIdx_of_ge hj b (not_lt.1 hb), dif_neg hb, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
  · rw [splitIdx_of_ge hj a (not_lt.1 ha), dif_neg ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj b hb, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, if_neg]
      intro hab; subst hab; exact ha hb
    · rw [splitIdx_of_ge hj b (not_lt.1 hb), Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
      · intro h; subst h; rfl

theorem blockMat_mul (hj : j ≤ n) (h₁ h₂ : Matrix (Fin j) (Fin j) R) :
    blockMat hj (h₁ * h₂) = blockMat hj h₁ * blockMat hj h₂ := by
  rw [blockMat, blockMat, blockMat, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem blockMat_one (hj : j ≤ n) : blockMat hj (1 : Matrix (Fin j) (Fin j) R) = 1 := by
  rw [blockMat, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def blockGL (hj : j ≤ n) : GL (Fin j) R →* GL (Fin n) R :=
  Units.map
    { toFun := blockMat hj
      map_one' := blockMat_one hj
      map_mul' := blockMat_mul hj }

@[simp] theorem coe_blockGL (hj : j ≤ n) (h : GL (Fin j) R) :
    ((blockGL hj h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = blockMat hj h := rfl

theorem map_blockMat {S : Type*} [CommRing S] (f : R →+* S) (hj : j ≤ n)
    (h : Matrix (Fin j) (Fin j) R) : (blockMat hj h).map f = blockMat hj (h.map f) := by
  ext a b
  simp only [Matrix.map_apply, blockMat_apply]
  split_ifs <;> simp

theorem blockMat_blockMat {k : ℕ} (hk : k ≤ j) (hj : j ≤ n) (γ : Matrix (Fin k) (Fin k) R) :
    blockMat hj (blockMat hk γ) = blockMat (hk.trans hj) γ := by
  ext a b
  simp only [blockMat_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | omega | simp_all [Fin.ext_iff] | (exfalso; omega)

theorem uMat_colX_eq_blockMat {i : ℕ} (hi : i < j) (hj : j ≤ n) (ξ : Fin i → R) :
    uMat (colX (n := n) i ξ) = blockMat hj (uMat (colX (n := j) i ξ)) := by
  ext a b
  simp only [blockMat_apply, uMat_apply, colX_apply]
  split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])

def colBlock {j m : ℕ} (x : Fin j → R) : Matrix (Fin j) (Fin m) R :=
  Matrix.of fun i c => if c.val = 0 then x i else 0

theorem uMat_colX_eq_fromBlocks (hj : j < n) (x : Fin j → R) :
    uMat (colX (n := n) j x) = (Matrix.fromBlocks 1 (colBlock (m := n - j) x) 0 1).submatrix
      (splitIdx hj.le) (splitIdx hj.le) := by
  ext a b
  rw [Matrix.submatrix_apply, uMat_apply]
  by_cases ha : a.val < j
  · rw [splitIdx_of_lt hj.le a ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj.le b hb, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
    · rw [splitIdx_of_ge hj.le b (not_lt.1 hb), Matrix.fromBlocks_apply₁₂]
      simp only [colBlock, Matrix.of_apply, colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
  · rw [splitIdx_of_ge hj.le a (not_lt.1 ha)]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj.le b hb, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
    · rw [splitIdx_of_ge hj.le b (not_lt.1 hb), Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])

theorem mul_colBlock {m : ℕ} (h : Matrix (Fin j) (Fin j) R) (x : Fin j → R) :
    h * colBlock (m := m) x = colBlock (h.mulVec x) := by
  ext i c
  simp only [Matrix.mul_apply, colBlock, Matrix.of_apply, Matrix.mulVec, dotProduct]
  split_ifs <;> simp

theorem colGL_mul_blockGL (hj : j < n) (h : GL (Fin j) R) (x : Fin j → R) :
    colGL (n := n) j x * blockGL hj.le h =
      blockGL hj.le h * colGL j (((h⁻¹ : GL (Fin j) R) : Matrix (Fin j) (Fin j) R).mulVec x) := by
  refine Units.ext ?_
  simp only [Units.val_mul, colGL, coe_uGL, coe_blockGL]
  rw [uMat_colX_eq_fromBlocks hj, uMat_colX_eq_fromBlocks hj, blockMat, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, mul_colBlock,
    Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  simp

theorem blockGL_blockGL {k : ℕ} (hk : k ≤ j) (hj : j ≤ n) (γ : GL (Fin k) R) :
    blockGL hj (blockGL hk γ) = blockGL (hk.trans hj) γ :=
  Units.ext (by
    simp only [coe_blockGL]
    exact blockMat_blockMat hk hj (γ : Matrix (Fin k) (Fin k) R))

theorem colGL_eq_blockGL {i : ℕ} (hi : i < j) (hj : j ≤ n) (ξ : Fin i → R) :
    colGL (n := n) i ξ = blockGL hj (colGL (n := j) i ξ) :=
  Units.ext (by
    simp only [colGL, coe_uGL, coe_blockGL]
    exact uMat_colX_eq_blockMat hi hj ξ)

end Block

end FourierWhittaker

end

end GroundTheory.Automorphic
end

section
open NumberField MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

theorem continuous_setIntegral_vecDomain {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [FirstCountableTopology X]
    {H : X → (ι → 𝔸[K]) → ℂ} (hH : Continuous (Function.uncurry H)) :
    Continuous fun x => ∫ y in vecDomain K ι, H x y ∂vecMeasure K ι := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.prod (isCompact_closure_vecDomain (K := K) (ι := ι))).exists_bound_of_continuousOn
    hH.continuousOn
  have : IsFiniteMeasure ((vecMeasure K ι).restrict (vecDomain K ι)) := ⟨by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  refine continuousAt_of_dominated (bound := fun _ => M)
    (Eventually.of_forall fun x => (hH.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ?_ (integrable_const M)
    (ae_of_all _ fun y => (hH.comp (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [hN] with x hx
  refine (ae_restrict_iff' measurableSet_vecDomain).2 (ae_of_all _ fun y hy => ?_)
  exact hM (x, y) ⟨hx, subset_closure hy⟩

variable {n : ℕ}

def lastVec (k : ℕ) : Fin k → K := fun i => if i.val + 1 = k then 1 else 0

def stepCoeff (k : ℕ) (F : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  vecCoeff (fun x : Fin k → 𝔸[K] => F (colGL k x * g)) (lastVec k)

def partialWhittakerCoeff (ϕ : AdelicGLn.AdelicGL K n → ℂ) : ℕ → AdelicGLn.AdelicGL K n → ℂ
  | 0 => ϕ
  | m + 1 => stepCoeff (n - 1 - m) (partialWhittakerCoeff ϕ m)

def partialCoeff (ϕ : AdelicGLn.AdelicGL K n → ℂ) (k : ℕ) : AdelicGLn.AdelicGL K n → ℂ :=
  partialWhittakerCoeff ϕ (n - k)

theorem partialCoeff_self (ϕ : AdelicGLn.AdelicGL K n → ℂ) : partialCoeff ϕ n = ϕ := by
  simp [partialCoeff, partialWhittakerCoeff]

theorem partialCoeff_of_lt (ϕ : AdelicGLn.AdelicGL K n → ℂ) {k : ℕ} (hk : k < n) :
    partialCoeff ϕ k = stepCoeff k (partialCoeff ϕ (k + 1)) := by
  rw [partialCoeff, partialCoeff, show n - k = (n - (k + 1)) + 1 by omega, partialWhittakerCoeff,
    show n - 1 - (n - (k + 1)) = k by omega]

theorem continuous_colGL (k : ℕ) :
    Continuous fun x : Fin k → 𝔸[K] => (colGL (n := n) k x : AdelicGLn.AdelicGL K n) := by
  have hc : ∀ (a b : Fin n), Continuous fun x : Fin k → 𝔸[K] => uMat (colX (n := n) k x) a b := by
    intro a b
    simp only [uMat_apply, colX_apply]
    by_cases h1 : a = b
    · simp only [h1, if_true]; exact continuous_const
    · simp only [h1, if_false]
      by_cases h2 : a < b
      · simp only [h2, dite_true]
        by_cases h3 : b.val = k
        · simp only [h3, dite_true]; exact continuous_apply _
        · simp only [h3, dite_false]; exact continuous_const
      · simp only [h2, dite_false]; exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_pi fun a => continuous_pi fun b => hc a b, ?_⟩
  have : (fun x : Fin k → 𝔸[K] => (((colGL (n := n) k x)⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K])) = fun x => uMat (colX (n := n) k (-x)) := by
    funext x; rw [← colGL_neg]; rfl
  rw [this]
  exact continuous_pi fun a => continuous_pi fun b => (hc a b).comp continuous_neg

instance firstCountableTopology_adelicGL : FirstCountableTopology (AdelicGLn.AdelicGL K n) := by
  have h1 : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝔸[K]) := inferInstance
  have h2 : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝔸[K])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) 𝔸[K])).symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (AdelicGLn.AdelicGL K n) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  infer_instance

theorem continuous_stepCoeff (k : ℕ) {F : AdelicGLn.AdelicGL K n → ℂ} (hF : Continuous F) :
    Continuous (stepCoeff k F) := by
  unfold stepCoeff vecCoeff
  haveI : LocallyCompactSpace (AdelicGLn.AdelicGL K n) := AdelicGLn.locallyCompactSpace K n
  exact continuous_setIntegral_vecDomain (H := fun g x => F (colGL k x * g) *
    (GroundTheory.Global.adelicChar K (-pair (lastVec k) x) : ℂ))
    ((hF.comp ((continuous_colGL k).comp continuous_snd |>.mul continuous_fst)).mul
      ((continuous_adelicChar_neg_pair _).comp continuous_snd))

theorem continuous_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) (k : ℕ) :
    Continuous (partialCoeff ϕ k) := by
  unfold partialCoeff
  induction n - k with
  | zero => exact hϕ
  | succ m ih => exact continuous_stepCoeff _ ih

theorem pair_matVec [DecidableEq ι] (ξ : ι → K) (M : Matrix ι ι K) (x : ι → 𝔸[K]) :
    pair ξ (matVec M x) = pair (Matrix.vecMul ξ M) x := by
  simp only [pair, matVec_apply, Finset.mul_sum, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

def IsLastRowUnit {j : ℕ} (h : Matrix (Fin j) (Fin j) K) : Prop :=
  Matrix.vecMul (lastVec j) h = lastVec j

theorem vecMul_lastVec {j : ℕ} (M : Matrix (Fin j) (Fin j) K) (c : Fin j) (hj : 0 < j) :
    Matrix.vecMul (lastVec j) M c = M ⟨j - 1, by omega⟩ c := by
  simp only [Matrix.vecMul, dotProduct, lastVec]
  rw [Finset.sum_eq_single ⟨j - 1, by omega⟩]
  · simp; omega
  · intro r _ hr
    rw [if_neg, zero_mul]
    intro h; apply hr; ext; simp; omega
  · simp

theorem IsLastRowUnit.inv {j : ℕ} {h : GL (Fin j) K} (hh : IsLastRowUnit (h : Matrix (Fin j) (Fin j) K)) :
    IsLastRowUnit ((h⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  unfold IsLastRowUnit at *
  conv_lhs => rw [← hh]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem isLastRowUnit_blockMat {j : ℕ} (h : Matrix (Fin j) (Fin j) K) :
    IsLastRowUnit (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  funext c
  rw [vecMul_lastVec _ _ (Nat.succ_pos j)]
  simp only [blockMat_apply, lastVec]
  split_ifs <;> (first | rfl | (exfalso; (try simp only [Fin.ext_iff, Fin.lt_def] at *); omega) | ((try simp only [Fin.ext_iff, Fin.lt_def] at *); omega) | simp_all [Fin.ext_iff])

theorem isLastRowUnit_colX {j : ℕ} (ξ : Fin j → K) :
    IsLastRowUnit (uMat (colX (n := j + 1) j ξ)) := by
  funext c
  rw [vecMul_lastVec _ _ (Nat.succ_pos j)]
  simp only [uMat_apply, lastVec, colX_apply]
  split_ifs <;> (first | rfl | (exfalso; (try simp only [Fin.ext_iff, Fin.lt_def] at *); omega) | ((try simp only [Fin.ext_iff, Fin.lt_def] at *); omega) | simp_all [Fin.ext_iff])

theorem blockMat_self (h : Matrix (Fin n) (Fin n) K) : blockMat (le_refl n) h = h := by
  ext a b
  rw [blockMat_apply, dif_pos a.2, dif_pos b.2]

theorem diagonal_blockGL {j : ℕ} (hj : j ≤ n) (h : GL (Fin j) K) :
    AdelicGLn.diagonal K n (blockGL hj h) =
      blockGL hj (Matrix.GeneralLinearGroup.map (algebraMap K 𝔸[K]) h) := by
  refine Units.ext ?_
  ext a b
  rw [AdelicGLn.diagonal_apply, coe_blockGL, coe_blockGL, blockMat_apply, blockMat_apply]
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

theorem diagonal_colGL (k : ℕ) (ξ : Fin k → K) :
    AdelicGLn.diagonal K n (colGL k ξ) = colGL k (fun i => algebraMap K 𝔸[K] (ξ i)) := by
  refine Units.ext ?_
  ext a b
  rw [AdelicGLn.diagonal_apply, ← map_colGL (algebraMap K 𝔸[K]), Matrix.map_apply]

theorem mulVec_map_inv {j : ℕ} (h : GL (Fin j) K) (x : Fin j → 𝔸[K]) :
    ((((Matrix.GeneralLinearGroup.map (algebraMap K 𝔸[K]) h)⁻¹ : GL (Fin j) 𝔸[K])) :
      Matrix (Fin j) (Fin j) 𝔸[K]).mulVec x = matVec ((h⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) x := by
  rw [← map_inv]
  rfl

theorem stepCoeff_diagonal_blockGL {j : ℕ} (hj : j < n) (h : GL (Fin j) K)
    {F : AdelicGLn.AdelicGL K n → ℂ}
    (hB : ∀ g, F (AdelicGLn.diagonal K n (blockGL hj.le h) * g) = F g)
    (hC : ∀ (ξ : Fin j → K) g, F (AdelicGLn.diagonal K n (colGL j ξ) * g) = F g)
    (g : AdelicGLn.AdelicGL K n) :
    stepCoeff j F (AdelicGLn.diagonal K n (blockGL hj.le h) * g) =
      vecCoeff (fun y => F (colGL j y * g)) (Matrix.vecMul (lastVec j) (h : Matrix (Fin j) (Fin j) K)) := by
  set e := lastVec (K := K) j
  set H : (Fin j → 𝔸[K]) → ℂ := fun y => F (colGL j y * g) *
    (GroundTheory.Global.adelicChar K (-pair e (matVec (h : Matrix (Fin j) (Fin j) K) y)) : ℂ)
  have hH : ∀ l ∈ vecLattice K (Fin j), ∀ y, H (l + y) = H y := by
    intro l hl y
    obtain ⟨ξ, rfl⟩ := mem_vecLattice.1 hl
    have h1 : GroundTheory.Global.adelicChar K (-pair e (matVec (h : Matrix (Fin j) (Fin j) K)
        (fun i => algebraMap K 𝔸[K] (ξ i)))) = 1 := by
      rw [matVec_algebraMap, pair_algebraMap, ← map_neg, GroundTheory.Global.adelicChar_algebraMap]
    simp only [H]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, hC, matVec_add, pair_add, neg_add,
      AddChar.map_add_eq_mul, h1, one_mul]
  have hconj : ∀ x : Fin j → 𝔸[K], colGL j x * (AdelicGLn.diagonal K n (blockGL hj.le h) * g) =
      AdelicGLn.diagonal K n (blockGL hj.le h) *
        (colGL j (matVec ((h⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) x) * g) := by
    intro x
    rw [← mul_assoc, diagonal_blockGL, colGL_mul_blockGL hj, mulVec_map_inv, mul_assoc]
  have hmv : ∀ x : Fin j → 𝔸[K], matVec (h : Matrix (Fin j) (Fin j) K)
      (matVec ((h⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) x) = x := by
    intro x
    rw [← matVec_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, matVec_one]
  unfold stepCoeff vecCoeff
  simp_rw [hconj, hB]
  have := setIntegral_comp_matVec (h⁻¹) hH
  simp only [H, hmv] at this
  rw [this]
  simp only [H, pair_matVec]

open AutomorphicForm in

theorem partialCoeff_diagonal_blockGL {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsLeftInvariant ϕ) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) K),
      (IsLastRowUnit (h : Matrix (Fin j) (Fin j) K) ∨ j = n) → ∀ g,
        partialCoeff ϕ j (AdelicGLn.diagonal K n (blockGL hj h) * g) = partialCoeff ϕ j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h _ g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this, hϕ]
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    have hlast : IsLastRowUnit (h : Matrix (Fin j) (Fin j) K) := hh.resolve_right (by omega)
    rw [partialCoeff_of_lt ϕ hjn]
    have hB : ∀ g, partialCoeff ϕ (j + 1) (AdelicGLn.diagonal K n (blockGL hjn.le h) * g) =
        partialCoeff ϕ (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (Or.inl (isLastRowUnit_blockMat _)) g
    have hC : ∀ (ξ : Fin j → K) g, partialCoeff ϕ (j + 1) (AdelicGLn.diagonal K n (colGL j ξ) * g) =
        partialCoeff ϕ (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (Or.inl (isLastRowUnit_colX _)) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hlast]
    rfl

open AutomorphicForm in

theorem partialCoeff_succ_diagonal_colGL {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsLeftInvariant ϕ)
    {k : ℕ} (hk : k < n) (ξ : Fin k → K) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ (k + 1) (AdelicGLn.diagonal K n (colGL k ξ) * g) = partialCoeff ϕ (k + 1) g := by
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_diagonal_blockGL hϕ _ (k + 1) rfl hk _ (Or.inl (isLastRowUnit_colX _)) g

open AutomorphicForm in

theorem partialCoeff_succ_diagonal_blockGL {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsLeftInvariant ϕ) {k : ℕ} (hk : k < n) (γ : GL (Fin k) K) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ (k + 1) (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) =
      partialCoeff ϕ (k + 1) g := by
  rw [← blockGL_blockGL (Nat.le_succ k) hk]
  exact partialCoeff_diagonal_blockGL hϕ _ (k + 1) rfl hk _ (Or.inl (isLastRowUnit_blockMat _)) g

open AutomorphicForm in

theorem partialCoeff_diagonal_blockGL_eq_vecCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsLeftInvariant ϕ) {k : ℕ} (hk : k < n) (γ : GL (Fin k) K) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) =
      vecCoeff (fun y => partialCoeff ϕ (k + 1) (colGL k y * g))
        (Matrix.vecMul (lastVec k) (γ : Matrix (Fin k) (Fin k) K)) := by
  rw [partialCoeff_of_lt ϕ hk]
  exact stepCoeff_diagonal_blockGL hk γ (partialCoeff_succ_diagonal_blockGL hϕ hk γ)
    (partialCoeff_succ_diagonal_colGL hϕ hk) g

end FourierWhittaker

end

end GroundTheory.Automorphic
end
