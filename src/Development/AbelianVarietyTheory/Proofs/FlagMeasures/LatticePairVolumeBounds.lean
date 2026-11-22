module

public import Mathlib
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentSmulMemOfTraceIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCoveringOfTraceDualLowerBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTer

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
namespace GlobalTheory.HomCover

def toMat {R : Type} {a b : ℕ} (y : Fin b × Fin a → R) : Matrix (Fin b) (Fin a) R :=
  Matrix.of fun i j => y (i, j)

theorem toMat_add {R : Type} [Add R] {a b : ℕ} (y z : Fin b × Fin a → R) :
    toMat (y + z) = toMat y + toMat z := rfl

theorem toMat_smul {S R : Type} [SMul S R] {a b : ℕ} (s : S) (y : Fin b × Fin a → R) :
    toMat (s • y) = s • toMat y := rfl

theorem toMat_entries {R : Type} {a b : ℕ} (φ : Matrix (Fin b) (Fin a) R) :
    toMat (fun p : Fin b × Fin a => φ p.1 p.2) = φ := rfl

theorem dot_eq_trace {R : Type} [CommRing R] {a b : ℕ} (f y : Fin b × Fin a → R) :
    f ⬝ᵥ y = Matrix.trace (toMat y * (toMat f)ᵀ) := by
  simp [dotProduct, Matrix.trace, Matrix.mul_apply, toMat, Fintype.sum_prod_type, mul_comm]

def homLat {K : Type} [Field K] [NumberField K] {a b : ℕ} (A : Submodule (𝓞 K) (Fin a → K))
    (B : Submodule (𝓞 K) (Fin b → K)) : Submodule (𝓞 K) (Fin b × Fin a → K) where
  carrier := {y | ∀ x ∈ A, toMat y *ᵥ x ∈ B}
  add_mem' := fun {y z} hy hz x hx => by
    rw [toMat_add, Matrix.add_mulVec]; exact B.add_mem (hy x hx) (hz x hx)
  zero_mem' := fun x hx => by
    have : toMat (0 : Fin b × Fin a → K) = 0 := rfl
    rw [this, Matrix.zero_mulVec]; exact B.zero_mem
  smul_mem' := fun s y hy x hx => by
    rw [toMat_smul, Matrix.smul_mulVec]; exact B.smul_mem s (hy x hx)

theorem homLat_fg {K : Type} [Field K] [NumberField K] {a b : ℕ}
    (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (hA : A.FG) (hB : B.FG)
    (hAs : Submodule.span K (A : Set (Fin a → K)) = ⊤) : (homLat A B).FG := by
  obtain ⟨s, rfl⟩ := hA
  let F : (Fin b × Fin a → K) →ₗ[𝓞 K] (s → Fin b → K) :=
    { toFun := fun y x => toMat y *ᵥ x
      map_add' := fun y z => by ext1 x; simp [toMat_add, Matrix.add_mulVec]
      map_smul' := fun c y => by ext1 x; simp [toMat_smul, Matrix.smul_mulVec] }
  have hF : Function.Injective F := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    rw [Submodule.span_span_of_tower] at hAs
    have : Matrix.toLin' (toMat y) = 0 := by
      refine LinearMap.ext_on hAs fun x hx => ?_
      exact congrFun hy ⟨x, hx⟩
    have h0 : toMat y = 0 := by simpa using this
    funext p
    exact congrFun (congrFun h0 p.1) p.2
  refine Submodule.fg_of_fg_map_injective F hF ?_
  have hP : (Submodule.pi Set.univ (fun _ : s => B)).FG := Submodule.fg_pi fun _ => hB
  refine hP.of_le ?_
  rintro _ ⟨y, hy, rfl⟩ x _
  exact hy x (Submodule.subset_span x.2)

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {b : ℕ}
    (B : Submodule (𝓞 K) (Fin b → K)) (hBs : Submodule.span K (B : Set (Fin b → K)) = ⊤)
    (v : Fin b → K) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ B := by
  first
  | exact @_root_.GlobalTheory.FiniteSumFlagMeasures.main
  | exact _root_.GlobalTheory.FiniteSumFlagMeasures.main
  | (apply _root_.GlobalTheory.FiniteSumFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSumFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSumFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSumFlagMeasures.main ..)

theorem homLat_span {K : Type} [Field K] [NumberField K] {a b : ℕ}
    (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (hA : A.FG)
    (hBs : Submodule.span K (B : Set (Fin b → K)) = ⊤) :
    Submodule.span K (homLat A B : Set (Fin b × Fin a → K)) = ⊤ := by
  classical
  obtain ⟨s, rfl⟩ := hA
  rw [eq_top_iff]
  intro y _
  choose d hd0 hd using fun x : Fin a → K => exists_smul_mem B hBs (toMat y *ᵥ x)
  have hD : ∏ x ∈ s, d x ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hd0 x
  have hmem : (∏ x ∈ s, d x) • y ∈ homLat (Submodule.span (𝓞 K) (s : Set (Fin a → K))) B := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [toMat_smul, Matrix.smul_mulVec, ← Finset.prod_erase_mul s d hx, mul_smul]
      exact B.smul_mem _ (hd x)
    | zero => simp
    | add x z _ _ hx hz => rw [Matrix.mulVec_add]; exact B.add_mem hx hz
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact B.smul_mem _ hx
  have h1 : algebraMap (𝓞 K) K (∏ x ∈ s, d x) ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have : y = (algebraMap (𝓞 K) K (∏ x ∈ s, d x))⁻¹ • ((∏ x ∈ s, d x) • y) := by
    rw [← algebraMap_smul K (∏ x ∈ s, d x) y, smul_smul, inv_mul_cancel₀ h1, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

noncomputable def frameEquiv {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    (Fin b × Fin a → ℂ) ≃ₗ[ℂ] (Fin b × Fin a → ℂ) where
  toFun y p := (P⁻¹ * toMat y * Q) p.1 p.2
  invFun y p := (P * toMat y * Q⁻¹) p.1 p.2
  map_add' y z := by
    funext p; rw [toMat_add, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c y := by
    funext p; rw [toMat_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv y := by
    funext p
    simp only [toMat_entries]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ hP]
    rfl
  right_inv y := by
    funext p
    simp only [toMat_entries]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hQ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hP]
    rfl

theorem toMat_frameEquiv {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (y : Fin b × Fin a → ℂ) :
    toMat (frameEquiv P Q hP hQ y) = P⁻¹ * toMat y * Q := rfl

theorem dual_coord {a b : ℕ} (P : Matrix (Fin b) (Fin b) ℂ) (Q : Matrix (Fin a) (Fin a) ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (f c : Fin b × Fin a → ℂ)
    (h : ∀ y, f ⬝ᵥ y = c ⬝ᵥ frameEquiv P Q hP hQ y) :
    c = fun p => (Q⁻¹ * (toMat f)ᵀ * P) p.2 p.1 := by
  refine dotProduct_eq _ _ fun z => ?_
  obtain ⟨y, rfl⟩ := (frameEquiv P Q hP hQ).surjective z
  rw [← h, dot_eq_trace, dot_eq_trace, toMat_frameEquiv]
  have : (toMat fun p : Fin b × Fin a => (Q⁻¹ * (toMat f)ᵀ * P) p.2 p.1)ᵀ
      = Q⁻¹ * (toMat f)ᵀ * P := rfl
  rw [this, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ P]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hQ, Matrix.mul_nonsing_inv_cancel_left _ _ hP]

end GlobalTheory.HomCover
