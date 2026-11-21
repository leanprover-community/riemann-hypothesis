import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsIsoCols (C : Matrix (Fin n) (Fin r) E) : Prop :=
  LinearIndependent E Cᵀ ∧ cT (σ : E →+* E) C * J * C = 0

def unipSet (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Set (GAd σ J) :=
  {g | (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      ((matHom _ σ J g).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = adMat F C *ᵥ a) ∧
    ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
      ∃ a, ((matHom _ σ J g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F C *ᵥ a}

def unipFlag (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) := Subgroup.closure (unipSet σ J C d)

def parFlag (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) where
  carrier := {p | (∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J p).1 * adMat F C = adMat F C * B) ∧
    ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ (matHom _ σ J p⁻¹).1 * adMat F C = adMat F C * B}
  one_mem' := ⟨⟨1, blockTriangular_one, by simp⟩, 1, blockTriangular_one, by simp⟩
  mul_mem' := fun {p q} ⟨⟨A, hA, eA⟩, A', hA', eA'⟩ ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ =>
    ⟨⟨A * B, hA.mul hB, by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, eB, ← Matrix.mul_assoc, eA, Matrix.mul_assoc]⟩,
      B' * A', hB'.mul hA', by
        rw [_root_.mul_inv_rev, map_mul, Units.val_mul, Matrix.mul_assoc, eA', ← Matrix.mul_assoc, eB', Matrix.mul_assoc]⟩
  inv_mem' := fun {p} h => ⟨h.2, by rw [inv_inv]; exact h.1⟩

def leviFlag (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) := parFlag σ J X d ⊓ parFlag σ J Y d

def leftGrp (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) : Subgroup (GAd σ J) :=
  unipFlag σ J C d ⊔ (ratPts σ J ⊓ parFlag σ J C d)

def adjA : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (AF F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (AF F)) * cT (sigR (AF F) σ) X * J.map (inclR (F := F) (AF F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (j : Fin r) :
    Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (C * single j j (1 : E) * L).map (inclR (F := F) (AF F))

variable {σ J}

omit [NumberField E] in
theorem adjA_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J X =
    J⁻¹.map (inclR (F := F) (AF F)) * cT (sigR (AF F) σ) X * J.map (inclR (F := F) (AF F)) := rfl

omit [NumberField E] in
theorem adjA_map (X : Matrix (Fin n) (Fin n) E) : adjA σ J (X.map (inclR (F := F) (AF F))) =
    (J⁻¹ * cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F)) := by
  rw [adjA_apply, GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.map_mul, Matrix.map_mul]

omit [NumberField E] in
theorem idemA_eq (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (j : Fin r) :
    idemA (F := F) C L j = C.map (inclR (F := F) (AF F)) * single j j (1 : AF F ⊗[F] E) * L.map (inclR (F := F) (AF F)) := by
  rw [idemA, Matrix.map_mul, Matrix.map_mul, Matrix.map_single, map_one]

omit [NumberField E] in
theorem sum_idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) :
    ∑ j, idemA (F := F) C L j = (C * L).map (inclR (F := F) (AF F)) := by
  simp only [idemA_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one, Matrix.map_mul]

theorem lower_iff {C : Matrix (Fin n) (Fin r) E} {d : Fin r → ℕ} {m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} :
    (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      m *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = adMat F C *ᵥ a) ↔
    ∃ A : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), (∀ j i, d i ≤ d j → A j i = 0) ∧ m * adMat F C = adMat F C * A := by
  constructor
  · intro h
    choose a ha e using h
    exact ⟨of fun j i => a i j, fun j i => ha i j, Matrix.ext fun k i => congrFun (e i) k⟩
  · rintro ⟨A, hA, e⟩ i
    exact ⟨fun j => A j i, fun j => hA j i, funext fun k => congrFun (congrFun e k) i⟩

theorem form_mul_of_mul_cols {C : Matrix (Fin n) (Fin r) E} {g : GAd σ J} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (h : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g⁻¹).1 = cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) := by
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hi : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := Units.mul_inv g.1
  have e : adMat F J * (matHom _ σ J g⁻¹).1 = cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J := by
    conv_lhs => rw [← hg, Matrix.mul_assoc, hi, Matrix.mul_one]
  rw [adMat, Matrix.map_mul, ← GlobalTheory.AutFunCounterexample.cT_map_gen, Matrix.mul_assoc, e, ← Matrix.mul_assoc, ← cT_mul, h, cT_mul,
    Matrix.mul_assoc]

theorem unipFlag_const (C : Matrix (Fin n) (Fin r) E) (c : ℕ) : unipFlag σ J C (fun _ => c) = unipRad σ J C := by
  rw [unipFlag, unipRad]
  congr 1
  ext g
  have h1 : ∀ m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∃ A : Matrix (Fin r) (Fin r) (AF F ⊗[F] E),
      (∀ j i, c ≤ c → A j i = 0) ∧ m * adMat F C = adMat F C * A) ↔ m * adMat F C = 0 := fun m =>
    ⟨fun ⟨A, hA, e⟩ => by rw [e, show A = 0 from Matrix.ext fun j i => hA j i le_rfl, Matrix.mul_zero],
      fun e => ⟨0, fun _ _ _ => rfl, by rw [e, Matrix.mul_zero]⟩⟩
  refine (and_congr (lower_iff.trans (h1 _)) Iff.rfl).trans ⟨fun h => ⟨h.1, ?_, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have e : (matHom _ σ J g).1 * adMat F C = adMat F C * (1 : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) := by
    have := h.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    rw [this, Matrix.mul_one]
  have e2 := form_mul_of_mul_cols e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  rw [cT_one, Matrix.one_mul] at e2
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  conv_lhs => rw [← e2, Matrix.mul_assoc, hi, Matrix.mul_one]

section Form

variable (hJ : IsHermND σ J)
include hJ

omit [NumberField F] [NumberField E] in
theorem det_isUnit : IsUnit J.det := IsUnit.mk0 _ hJ.2

omit [NumberField F] [NumberField E] in
theorem cT_form : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j

omit [NumberField F] [NumberField E] in
theorem cT_form_inv : cT (σ : E →+* E) J⁻¹ = J⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  nth_rewrite 2 [← cT_form hJ]
  rw [← cT_mul, Matrix.mul_nonsing_inv _ (det_isUnit hJ), cT_one]

omit [NumberField E] in
theorem form_mul_inv : J.map (inclR (F := F) (AF F)) * J⁻¹.map (inclR (F := F) (AF F)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (det_isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in
theorem inv_mul_form : J⁻¹.map (inclR (F := F) (AF F)) * J.map (inclR (F := F) (AF F)) = 1 :=
  mul_eq_one_comm.1 (form_mul_inv hJ)

omit [NumberField E] in
theorem adjA_mul (X Y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J (X * Y) = adjA σ J Y * adjA σ J X := by
  simp only [adjA_apply, cT_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (J.map _), form_mul_inv hJ, Matrix.one_mul]

omit [NumberField E] in
theorem adjA_mul_self_iff (g : GL (Fin n) (AF F ⊗[F] E)) : adjA σ J g.1 * g.1 = 1 ↔ g ∈ HR (AF F) σ J := by
  change _ ↔ cT _ g.1 * J.map _ * g.1 = J.map _
  rw [adjA_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _)]
  constructor
  · intro h
    have := congrArg (J.map (inclR (F := F) (AF F)) * ·) h
    simpa only [← Matrix.mul_assoc, form_mul_inv hJ, Matrix.one_mul, Matrix.mul_one] using this
  · intro h
    rw [h, inv_mul_form hJ]

theorem adjA_mat (g : GAd σ J) : adjA σ J (matHom _ σ J g).1 = (matHom _ σ J g⁻¹).1 :=
  (Units.inv_eq_of_mul_eq_one_left ((adjA_mul_self_iff hJ g.1).2 g.2)).symm

omit [NumberField E] in
theorem perp_iff_idemA (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E)
    (hL : L * C = 1) (m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    (∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 →
        ∃ a, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ↔
      (1 - (C * L).map (inclR (F := F) (AF F))) * m * (1 - adjA σ J ((C * L).map (inclR (F := F) (AF F)))) = 0 := by
  rw [adjA_map]
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : J⁻¹ * cT (σ : E →+* E) (C * L) * J = J⁻¹ * cT (σ : E →+* E) L * (cT (σ : E →+* E) C * J) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  have hT : cT (σ : E →+* E) C * J * (J⁻¹ * cT (σ : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (det_isUnit hJ), ← cT_mul, hL, cT_one]
  rw [e]
  generalize cT (σ : E →+* E) C * J = T at hT ⊢
  generalize J⁻¹ * cT (σ : E →+* E) L = P at hT ⊢
  have e1 : 1 - (P * T).map φ = (1 - P * T).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro h
    ext i k
    obtain ⟨a, ha⟩ := h (fun j => (1 - P * T : Matrix (Fin n) (Fin n) E) j k) (by
      have : T * (1 - P * T) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.mul_one, Matrix.one_mul, sub_self]
      funext j; exact congrFun (congrFun this j) k)
    have h2 : (1 - (C * L).map φ) * C.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.map_mul, Matrix.mul_assoc, hL', Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 := congrArg ((1 - (C * L).map φ) *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec] at h3
    rw [e1]
    exact congrFun h3 i
  · intro h x hx
    refine ⟨(L.map φ * m) *ᵥ fun i => φ (x i), ?_⟩
    have h1 : (T.map φ) *ᵥ (fun i => φ (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec φ T x i
      rw [hx] at this
      simpa [Function.comp_def] using this.symm
    have h2 := congrArg (· *ᵥ fun i => φ (x i)) h
    simp only [Matrix.zero_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.map_mul (L := P),
      ← Matrix.mulVec_mulVec _ (P.map φ), h1, Matrix.mulVec_zero, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc] at h2
    rw [h2, Matrix.mulVec_mulVec]

omit [NumberField E] in
theorem idemA_complete (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0) :
    CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA C L)) := by
  have e : ∀ j : Fin r, J⁻¹ * cT (σ : E →+* E) (C * single j j (1 : E) * L) * J =
      J⁻¹ * cT (σ : E →+* E) L * cT (σ : E →+* E) (single j j (1 : E)) * (cT (σ : E →+* E) C * J) := fun j => by
    rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
  have e2 : ∀ i j : Fin r, C * single i i (1 : E) * L * (C * single j j (1 : E) * L) =
      C * (single i i (1 : E) * single j j (1 : E)) * L := fun i j => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L C, hL, Matrix.one_mul]
  refine fam_complete (adjA_mul hJ) ⟨fun j => ?_, fun i j hij => ?_⟩ (fun i j => ?_) (fun i j => ?_)
  · show _ * _ = _
    rw [idemA, ← Matrix.map_mul, e2, Matrix.single_mul_single_same, one_mul]
  · show _ * _ = _
    rw [idemA, idemA, ← Matrix.map_mul, e2, Matrix.single_mul_single_of_ne (h := hij)]
    simp
  · rw [idemA, idemA, adjA_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at hLL ⊢
    rw [← Matrix.mul_assoc J⁻¹, ← Matrix.mul_assoc L, hLL]
    simp
  · rw [idemA, idemA, adjA_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at h0 ⊢
    rw [← Matrix.mul_assoc J C, ← Matrix.mul_assoc (cT _ C), h0]
    simp

variable (hσ : ∀ x, σ (σ x) = x)
include hσ

omit [NumberField E] in
theorem adjA_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : adjA σ J (adjA σ J X) = X := by
  have h : cT (sigR (AF F) σ) (cT (sigR (AF F) σ) X) = X := by
    ext i j
    show sigR (AF F) σ (sigR (AF F) σ (X i j)) = X i j
    induction X i j using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [adjA_apply, cT_mul, GlobalTheory.AutFunCounterexample.cT_map_gen, cT_form hJ, cT_form_inv hJ, h, Matrix.mul_assoc]
  rw [inv_mul_form hJ, Matrix.mul_one, ← Matrix.mul_assoc, inv_mul_form hJ, Matrix.one_mul]

omit [NumberField F] in

theorem exists_dualCols {C : Matrix (Fin n) (Fin r) E} (hC : IsIsoCols σ J C) :
    ∃ L : Matrix (Fin r) (Fin n) E, L * C = 1 ∧ L * J⁻¹ * cT (σ : E →+* E) L = 0 := by
  obtain ⟨hC, h0⟩ := hC
  have cc : ∀ {m p : Type} (A : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r) (Fin n) E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  set c := cT (m := Fin n) (p := Fin r) (σ : E →+* E) C with hcd
  set d := cT (σ : E →+* E) L with hd
  set s := L * J⁻¹ * d with hs
  have hu := det_isUnit hJ
  have hcd1 : c * d = 1 := by rw [hcd, hd, ← cT_mul, hL, cT_one]
  have hss : cT (σ : E →+* E) s = s := by
    rw [hs, cT_mul, cT_mul, hd, cc, cT_form_inv hJ, Matrix.mul_assoc]
  refine ⟨L - (1 / 2 : E) • (s * (c * J)), ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, h0, hL]; simp
  · have e : cT (σ : E →+* E) (L - (1 / 2 : E) • (s * (c * J))) = d - (1 / 2 : E) • (J * C * s) := by
      have : J * C * s = cT (σ : E →+* E) (s * (c * J)) := by
        rw [cT_mul, cT_mul, hss, cT_form hJ, hcd, cc]
      rw [this, hd]
      generalize s * (c * J) = X
      ext i j
      simp [cT, map_ofNat]
    have e1 : L * J⁻¹ * (J * C * s) = s := by
      rw [← Matrix.mul_assoc _ (J * C), ← Matrix.mul_assoc _ J,
        Matrix.nonsing_inv_mul_cancel_right _ _ hu, hL, Matrix.one_mul]
    have e2 : s * (c * J) * J⁻¹ = s * c := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
    have e3 : s * c * (J * C * s) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, ← Matrix.mul_assoc c, h0]; simp
    rw [e, Matrix.sub_mul, Matrix.smul_mul, e2, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, e1,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, e3, Matrix.mul_assoc s, hcd1, ← hs, Matrix.mul_one]
    module

theorem mem_unipSet_iff (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GAd σ J) :
    g ∈ unipSet σ J C d ↔ (matHom _ σ J g).1 - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 := by
  rw [mem_raise_fam (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA_complete hJ C L hL h0 hLL) hd, sum_idemA,
    ← perp_iff_idemA hJ C L hL, map_sub, adjA_mat hJ, GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ)]
  have hinv : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  unfold unipSet adMat
  rw [Set.mem_ofPred_eq]
  generalize (matHom _ σ J g⁻¹).1 = y at hinv ⊢
  generalize (matHom _ σ J g).1 = x at hinv ⊢
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have sw : ∀ (m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin r),
      idemA C L j * m * idemA C L i = 0 ↔ (L.map φ * m * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 :=
    fun m i j => by rw [idemA_eq, idemA_eq]; exact sandwich_eq_zero hL' m i j
  simp only [sw]
  have co : ∀ (i : Fin r) (a : Fin r → AF F ⊗[F] E), (x - 1) *ᵥ (fun k => φ (C k i)) = C.map φ *ᵥ a →
      ∀ j, (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = a j := fun i a ha j => by
    have := congrArg (L.map φ *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
    exact congrFun this j
  constructor
  · rintro ⟨h1, h2⟩
    have k : ∀ i j : Fin r, d i ≤ d j →
        (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 := fun i j hij => by
      obtain ⟨a, ha, ha'⟩ := h1 i
      rw [co i a ha', ha j hij]
    refine ⟨h2, k, triangular_inv d _ _ ?_ k⟩
    have e : (x - 1) * C.map φ = C.map φ * (L.map φ * (x - 1) * C.map φ) := by
      ext k i
      obtain ⟨a, -, ha'⟩ := h1 i
      rw [Matrix.mul_apply (M := C.map φ)]
      simp only [co i a ha']
      exact congrFun ha' k
    have e' : y - 1 = -(x - 1) - (y - 1) * (x - 1) := by
      rw [sub_mul, mul_sub, hinv]; noncomm_ring
    rw [Matrix.mul_assoc (L.map φ * (y - 1)), ← e]
    conv_lhs => rw [e']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rintro ⟨h2, h1, -⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨a, ha⟩ := h2 (fun k => C k i) (funext fun j => congrFun (congrFun h0 j) i)
    exact ⟨a, fun j hij => by rw [← co i a ha, h1 i j hij], ha⟩

theorem mem_unipFlag_iff_raise (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) (hL : L * C = 1)
    (h0 : cT (σ : E →+* E) C * J * C = 0) (hLL : L * J⁻¹ * cT (σ : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GAd σ J) :
    g ∈ unipFlag σ J C d ↔ (matHom _ σ J g).1 - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 := by
  have he := idemA_complete hJ C L hL h0 hLL
  refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure ((mem_unipSet_iff hJ hσ C L hL h0 hLL hd g).2 hg)⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_unipSet_iff hJ hσ C L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul, Units.val_mul]
    generalize (matHom _ σ J x).1 = a at hx ⊢
    generalize (matHom _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adjA_mul hJ) (adjA_adjA hJ hσ)
      (fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) C L) d M) 0 hx
    rwa [map_sub, adjA_mat hJ, GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ)] at this

variable {C : Matrix (Fin n) (Fin r) E} (hC : IsIsoCols σ J C) (d : Fin r → ℕ)
include hC

theorem mem_unipFlag {g : GAd σ J} : g ∈ unipFlag σ J C d ↔ g ∈ unipSet σ J C d := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
  have hd : ∀ j, d j < M + 1 := fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)
  rw [mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd, mem_unipSet_iff hJ hσ C L hL hC.2 hLL hd]

theorem unipFlag_le_parFlag : unipFlag σ J C d ≤ parFlag σ J C d := by
  have key : ∀ g ∈ unipFlag σ J C d, ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧
      (matHom _ σ J g).1 * adMat F C = adMat F C * B := fun g hg => by
    obtain ⟨A, hA, e⟩ := lower_iff.1 ((mem_unipFlag hJ hσ hC d).1 hg).1
    refine ⟨A + 1, BlockTriangular.add (fun i j h => hA i j h.le) blockTriangular_one, ?_⟩
    rw [Matrix.mul_add, ← e, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, sub_add_cancel]
  exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩

theorem conj_mem_unipFlag {p u : GAd σ J} (hp : p ∈ parFlag σ J C d) (hu : u ∈ unipFlag σ J C d) :
    p * u * p⁻¹ ∈ unipFlag σ J C d := by
  obtain ⟨L, hL, -⟩ := exists_dualCols hJ hσ hC
  obtain ⟨h1, h2⟩ := (mem_unipFlag hJ hσ hC d).1 hu
  obtain ⟨A, hA, eA⟩ := lower_iff.1 h1
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have hi : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := Units.mul_inv p.1
  have e : (matHom _ σ J (p * u * p⁻¹)).1 - 1 =
      (matHom _ σ J p).1 * ((matHom _ σ J u).1 - 1) * (matHom _ σ J p⁻¹).1 := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hi]
  refine Subgroup.subset_closure ⟨lower_iff.2 ⟨B * A * B', fun j i hij => ?_, ?_⟩, fun x hx => ?_⟩
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases a : d k < d j
    · rw [hB a, zero_mul, zero_mul]
    by_cases b : d i < d l
    · rw [hB' b, mul_zero]
    rw [hA k l (by omega), mul_zero, zero_mul]
  · rw [e, Matrix.mul_assoc, eB', ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (adMat F C), eA, ← Matrix.mul_assoc, eB]
    simp only [Matrix.mul_assoc]
  · have h3 := (perp_iff_idemA hJ C L hL _).1 h2
    set φ := inclR (F := F) (E := E) (AF F)
    set y := (matHom _ σ J p⁻¹).1 *ᵥ fun i => φ (x i) with hy
    have h4 : adMat F (cT (σ : E →+* E) C * J) *ᵥ y = 0 := by
      have : adMat F (cT (σ : E →+* E) C * J) *ᵥ (fun i => φ (x i)) = 0 := funext fun i => by
        have := RingHom.map_mulVec φ (cT (σ : E →+* E) C * J) x i
        rw [hx] at this
        simpa [Function.comp_def] using this.symm
      rw [hy, Matrix.mulVec_mulVec, form_mul_of_mul_cols eB, ← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero]
    have h5 : adjA σ J ((C * L).map φ) *ᵥ y = 0 := by
      rw [adjA_map, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.map_mul, ← Matrix.mulVec_mulVec,
        h4, Matrix.mulVec_zero]
    have h6 := congrArg (· *ᵥ y) h3
    simp only [Matrix.zero_mulVec] at h6
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h5, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec] at h6
    refine ⟨B *ᵥ ((L.map φ * ((matHom _ σ J u).1 - 1)) *ᵥ y), ?_⟩
    rw [e, ← Matrix.mulVec_mulVec, ← hy, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (adMat F C),
      ← eB]

theorem isClosed_unipFlag : IsClosed (unipFlag σ J C d : Set (GAd σ J)) := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
  have hd : ∀ j, d j < M + 1 := fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  have e : (unipFlag σ J C d : Set (GAd σ J)) = ⋂ a, ⋂ b, ⋂ _ : wt d (M + 1) a ≤ wt d (M + 1) b + (0 : ℕ),
      {g | fam (adjA σ J) (idemA C L) a * ((matHom _ σ J g).1 - 1) * fam (adjA σ J) (idemA C L) b = 0} := by
    ext g
    simp only [Set.mem_iInter]
    exact mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd g
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_eq ((continuous_const.mul (hm.sub continuous_const)).mul continuous_const) continuous_const

theorem locallyCompact_unipFlag : LocallyCompactSpace (unipFlag σ J C d) :=
  (isClosed_unipFlag hJ hσ hC d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unipFlag : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipFlag σ J C d) := by
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨M, hd⟩ : ∃ M, ∀ j, d j < M := by
    obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
    exact ⟨M + 1, fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)⟩
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ C L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) C L) d M
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ C L hL hC.2 hLL hd
  obtain ⟨K', hK', k1, k2⟩ := compact_mod_of_weights (st := adjA σ J) (w := wt d M)
    (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K) hcont
    (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add, ← map_add, add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩) he
    (by
      have hu : ∀ j, idemA (F := F) C L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin r ⊕ Fin r, Sum.elim (idemA (F := F) C L) (fun j => adjA σ J (idemA C L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA C L)) (wt d M) 0 → unipFlag σ J C d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J C d → _ := fun n => Units.embedProduct _ (matHom _ σ J n.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine ⟨f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K'),
    hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_, fun u => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · have hu := (adjA_mul_self_iff hJ _).2 u.1.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J u.1).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 u.2⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : u = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1)⁻¹, inv_mem ?_, by rw [e, inv_mul_cancel_left]; exact ⟨k, hk, rfl⟩⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end Form

end GlobalTheory.UAut

end
end

section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.AutomorphicL2Unitary (LeftInv MemL2Quotient stdDom isFundamentalDomain_stdDom)
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ContDiff

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def IsSm (f : GAd σ J → ℂ) : Prop :=
  ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod)

variable {σ J} in

def dop (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : GAd σ J → ℂ :=
  fun g => z.sum fun l c => c * l.foldr lineDer f g

def IsCentral (z : List (ℝ → GAd σ J) →₀ ℂ) : Prop :=
  (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSm σ J f → ∀ a ∈ infPts σ J, ∀ g, dop z (fun x => f (x * a)) g = dop z f (g * a)

def IsMaxCpt (K : Subgroup (GAd σ J)) : Prop :=
  Maximal (fun K' : Subgroup (GAd σ J) => K' ≤ infPts σ J ∧ IsCompact (K' : Set (GAd σ J))) K

structure IsAut (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) : Prop where
  mod : IsSmoothModerate σ J φ
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k)))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})

structure IsAutOn (H K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ) : Prop where
  left : LeftInv H φ
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : IsSm σ J φ
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ N
  kfin : GlobalTheory.Doubling.IsKFinite K φ
  zfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ})

def IsConstTerm {r : ℕ} (C : Matrix (Fin n) (Fin r) E) (φ c : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (unipRad σ J C)) (𝓕 : Set (unipRad σ J C)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J C)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ g, c g = ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ

def IsConstTermOn (N : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf N) 𝓕 μ → μ 𝓕 = 1 →
    ∀ g, c g = ∫ u in 𝓕, φ ((u : GAd σ J) * g) ∂μ

def IsSqInt (φ : GAd σ J → ℂ) : Prop :=
  ∀ (μ : Measure (GAd σ J)) (𝓕 : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratPts σ J) 𝓕 μ →
    IntegrableOn (fun g => ‖φ g‖ ^ 2) 𝓕 μ

variable {σ J} {r : ℕ} {H H' K K' N : Subgroup (GAd σ J)} {φ c c' : GAd σ J → ℂ} {C : Matrix (Fin n) (Fin r) E}

omit [NumberField E] in

theorem kfin_iff : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => φ (g * k))) ↔
    GlobalTheory.Doubling.IsKFinite K φ := by
  rw [show (Set.range fun k : K => fun g => φ (g * k)) = {Ψ | ∃ k ∈ K, Ψ = fun g => φ (g * k)} from
    Set.ext fun Ψ => ⟨fun ⟨k, e⟩ => ⟨k, k.2, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨⟨k, hk⟩, e.symm⟩⟩]
  rfl

theorem isAut_iff_isAutOn : IsAut σ J K φ ↔ IsAutOn σ J (ratPts σ J) K φ :=
  ⟨fun h => ⟨h.mod.left, h.mod.level, h.mod.cont, h.mod.smooth, h.mod.growth, kfin_iff.1 h.kfin, h.zfin⟩,
    fun h => ⟨⟨h.left, h.level, h.cont, h.smooth, h.growth⟩, kfin_iff.2 h.kfin, h.zfin⟩⟩

theorem IsAutOn.mono (h : IsAutOn σ J H K φ) (hH : H' ≤ H) (hK : K' ≤ K) : IsAutOn σ J H' K' φ :=
  ⟨fun γ hγ => h.left γ (hH hγ), h.level, h.cont, h.smooth, h.growth,
    let ⟨W, hW, e⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h.kfin
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => e k (hK hk)⟩, h.zfin⟩

omit [NumberField E] in

theorem foldr_lineDer_char (hφ : ∀ g h, φ (g * h) = φ g * φ h) (a : ℂ) (l : List (ℝ → GAd σ J)) :
    ∃ b : ℂ, l.foldr lineDer (a • φ) = b • φ := by
  induction l with
  | nil => exact ⟨a, rfl⟩
  | cons γ l ih =>
    obtain ⟨b, h⟩ := ih
    refine ⟨b * deriv (fun t => φ (γ t)) 0, ?_⟩
    rw [List.foldr_cons, h]
    funext g
    simp only [lineDer, Pi.smul_apply, smul_eq_mul, hφ, ← mul_assoc, deriv_const_mul_field']
    ring

theorem isAut_of_char (K : Subgroup (GAd σ J)) (hφ : ∀ g h, φ (g * h) = φ g * φ h) (a : ℂ)
    (hm : IsSmoothModerate σ J (a • φ)) : IsAut σ J K (a • φ) := by
  refine ⟨hm, ?_, ?_⟩ <;> refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨a * φ k, funext fun g => by simp only [Pi.smul_apply, smul_eq_mul, hφ]; ring⟩
  · rintro _ ⟨z, -, rfl⟩
    choose b hb using foldr_lineDer_char hφ a
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l x => x * b l, funext fun g => by
      simp [dop, hb, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩

variable (σ J) in

theorem isAut_const (K : Subgroup (GAd σ J)) (a : ℂ) : IsAut σ J K fun _ => a := by
  have e : (fun _ => a) = a • fun _ : GAd σ J => (1 : ℂ) := funext fun _ => by simp
  exact e ▸ isAut_of_char K (by simp) a (e ▸ isSmoothModerate_const σ J a)

variable (σ J) in

theorem isAutOn_const (H K : Subgroup (GAd σ J)) (a : ℂ) : IsAutOn σ J H K fun _ => a :=
  { isAut_iff_isAutOn.1 (isAut_const σ J K a) with left := fun _ _ _ => rfl }

example : IsCentral σ J (Finsupp.single [] 1) :=
  ⟨by simp, fun f _ a _ g => by simp [dop]⟩

omit [NumberField E] in

theorem isMaxCpt_infPts (h : IsCompact (infPts σ J : Set (GAd σ J))) : IsMaxCpt σ J (infPts σ J) :=
  ⟨⟨le_rfl, h⟩, fun _ hK _ => hK.1⟩

theorem le_one_of_pow_mul_le {t a M : ℝ} (ha : 0 < a) (h : ∀ k : ℕ, t ^ k * a ≤ M) : t ≤ 1 := by
  by_contra ht
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 ht)).atTop_mul_const ha).eventually_gt_atTop M |>.exists
  exact hk.not_ge (h k)

open scoped ComplexOrder in

theorem eq_one_of_powers_compact {b Q : Matrix (Fin n) (Fin n) ℂ} {S : Set (Matrix (Fin n) (Fin n) ℂ)} (hS : IsCompact S)
    (hQ : Q * (bᴴ * b) = 1) (h1 : ∀ k : ℕ, (bᴴ * b) ^ k ∈ S) (h2 : ∀ k : ℕ, Q ^ k ∈ S) : bᴴ * b = 1 := by
  have hP := Matrix.posSemidef_conjTranspose_mul_self b
  have key : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (v : Fin n → ℂ), (∀ k : ℕ, A ^ k ∈ S) → v ≠ 0 → A *ᵥ v = t • v →
      t ≤ 1 := fun A t v hA hv e => by
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (f := fun X => X *ᵥ v)
      (continuous_id.matrix_mulVec continuous_const).continuousOn
    have hk : ∀ k : ℕ, A ^ k *ᵥ v = t ^ k • v := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    refine (le_abs_self t).trans (le_one_of_pow_mul_le (M := M) (norm_pos_iff.2 hv) fun k => ?_)
    have := hM _ (hA k)
    rwa [hk, norm_smul, norm_pow, Real.norm_eq_abs] at this
  have hev : ∀ j, hP.1.eigenvalues j = 1 := fun j => by
    have e := hP.1.mulVec_eigenvectorBasis j
    have hv : (hP.1.eigenvectorBasis j).ofLp ≠ 0 := fun h =>
      hP.1.eigenvectorBasis.orthonormal.ne_zero j ((WithLp.ofLp_eq_zero 2).1 h)
    have e2 := congrArg (Q *ᵥ ·) e
    simp only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, Matrix.mulVec_smul] at e2
    have h0 : hP.1.eigenvalues j ≠ 0 := fun h => hv (by rw [e2, h, zero_smul])
    have hpos := lt_of_le_of_ne (hP.eigenvalues_nonneg j) h0.symm
    have e3 : Q *ᵥ (hP.1.eigenvectorBasis j).ofLp = (hP.1.eigenvalues j)⁻¹ • (hP.1.eigenvectorBasis j).ofLp := by
      conv_rhs => rw [e2, inv_smul_smul₀ h0]
    exact le_antisymm (key _ _ _ h1 hv e) ((inv_le_one₀ hpos).1 (key _ _ _ h2 hv e3))
  rw [hP.1.spectral_theorem, show hP.1.eigenvalues = fun _ => 1 from funext hev]
  simp [Function.comp_def]

theorem conj_mem_UJ {R : Type} [CommRing R] {s : R →+* R} {A D : Matrix (Fin n) (Fin n) R} {c : GL (Fin n) R}
    (hc : Formalism.UG.cT s c.1 * A * c.1 = D) (g : GL (Fin n) R) : c⁻¹ * g * c ∈ Formalism.UG.UJ s D ↔ g ∈ Formalism.UG.UJ s A := by
  have h1 : Formalism.UG.cT s (c⁻¹).1 * Formalism.UG.cT s c.1 = 1 := by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  have e : Formalism.UG.cT s (c⁻¹ * g * c).1 * D * (c⁻¹ * g * c).1 = Formalism.UG.cT s c.1 * (Formalism.UG.cT s g.1 * A * g.1) * c.1 := by
    rw [← hc]
    simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc (Formalism.UG.cT s (c⁻¹).1), h1, Matrix.one_mul]
  change Formalism.UG.cT s _ * D * _ = D ↔ Formalism.UG.cT s g.1 * A * g.1 = A
  rw [e, ← hc]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg (fun X => Formalism.UG.cT s (c⁻¹).1 * X * (c⁻¹).1) h
  simpa only [← Matrix.mul_assoc, h1, Matrix.one_mul, Units.mul_inv_cancel_right] using this

variable (σ J) in

def majCpt (c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)) : Subgroup (GAd σ J) :=
  infPts σ J ⊓ ⨅ w, (stabArch σ J w (c w)).comap (projArch σ J w)

theorem mem_majCpt {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)} {g : GAd σ J} :
    g ∈ majCpt σ J c ↔ g ∈ infPts σ J ∧ ∀ w, projArch σ J w g ∈ stabArch σ J w (c w) := by
  simp [majCpt, Subgroup.mem_iInf]

theorem isMaxCpt_majCpt (h : IsCMExt F E σ) {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)}
    (hc : ∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) : IsMaxCpt σ J (majCpt σ J c) := by
  refine ⟨⟨inf_le_left, ?_⟩, fun K' hK' hle g hg => mem_majCpt.2 ⟨hK'.1 hg, fun w => ?_⟩⟩
  · convert (isCompact_univ_pi fun w => Frames.isCompact_stabArch h J w (c w)).image
      ((continuous_ofInf σ J).comp (continuous_embArchPi σ J)) using 1
    ext g
    refine ⟨fun hg => ⟨fun w => projArch σ J w g, fun w _ => (mem_majCpt.1 hg).2 w, GAd_ext σ J (fun w => by simp) fun v => ?_⟩, ?_⟩
    · simp [mem_infPts_iff_forall.1 hg.1 v]
    · rintro ⟨x, hx, rfl⟩
      exact mem_majCpt.2 ⟨mem_infPts.2 (projFin_ofInf _ _ _), fun w => by simpa using hx w trivial⟩
  obtain ⟨ε, hε⟩ := hc w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set D : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hcD : Formalism.UG.cT (sigR _ σ) D = D := by
    rw [hD, Formalism.UG.cT, diagonal_map (map_zero _), diagonal_transpose]
    congr 1; funext i; split_ifs <;> simp only [map_one, map_neg]
  let u : GL (Fin n) (w.Completion ⊗[F] E) := ⟨D, D, hDD, hDD⟩
  have hu : (c w)⁻¹ * (c w * u * (c w)⁻¹) * c w = u := by group
  let s₀ : GArch σ J w := ⟨c w * u * (c w)⁻¹, (conj_mem_UJ hε _).1 (hu.symm ▸ show _ * D * D = D by rw [hcD, hDD, one_mul])⟩
  have hs : embArch σ J w s₀ ∈ K' := hle (mem_majCpt.2 ⟨mem_infPts.2 (projFin_embArch _ _ _ _), fun v => by
    by_cases e : v = w
    · subst e
      rw [projArch_embArch_self, mem_stabArch]
      exact hu.symm ▸ show _ * 1 * D = 1 by rw [hcD, mul_one, hDD]
    · rw [projArch_embArch_ne σ J e]; exact one_mem _⟩)
  let m : GAd σ J →* GL (Fin n) (w.Completion ⊗[F] E) :=
    (MulAut.conj (c w)⁻¹).toMonoidHom.comp ((matHom _ σ J).comp (projArch σ J w))
  have hm : ∀ x, m x = (c w)⁻¹ * matHom _ σ J (projArch σ J w x) * c w := fun x => by simp [m]
  let f : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (infEmb τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp m)
  have hf : Continuous f := by
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    have e : f = fun x => (((c w)⁻¹).1 * (matHom _ σ J (projArch σ J w x)).1 * (c w).1).map (infEmb τ) :=
      funext fun x => congrArg (fun y : GL (Fin n) _ => y.1.map (infEmb τ)) (hm x)
    rw [e]
    exact ((continuous_const.matrix_mul (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
      (continuous_projArch σ J w)))).matrix_mul continuous_const).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
  have h1 : Formalism.UG.cT (sigR _ σ) (m g).1 * D * (m g).1 = D := hm g ▸ (conj_mem_UJ hε _).2 (projArch σ J w g).2
  let p := embArch σ J w s₀ * g⁻¹ * embArch σ J w s₀ * g
  have hp : p ∈ K' := mul_mem (mul_mem (mul_mem hs (inv_mem hg)) hs) hg
  have h2 : (m p).1 = Formalism.UG.cT (sigR _ σ) (m g).1 * (m g).1 := by
    have e : m (embArch σ J w s₀) = u := by rw [hm, projArch_embArch_self]; exact hu
    simp only [p, map_mul, map_inv, e, Units.val_mul]
    congr 1
    have e2 : D * ((m g)⁻¹).1 = Formalism.UG.cT (sigR _ σ) (m g).1 * D := by
      conv_lhs => rw [← h1, Units.mul_inv_cancel_right]
    exact (congrArg (· * D) e2).trans (by rw [Matrix.mul_assoc, hDD, Matrix.mul_one])
  have h3 : f p = (f g)ᴴ * f g := by
    change (m p).1.map (infEmb τ) = ((m g).1.map (infEmb τ))ᴴ * (m g).1.map (infEmb τ)
    rw [h2, Matrix.map_mul, Frames.map_cT_sigR h]
  have h4 : f p = 1 := h3 ▸ eq_one_of_powers_compact (Q := f p⁻¹) (hK'.2.image hf)
    (by rw [← h3, ← map_mul, inv_mul_cancel, map_one]) (fun k => ⟨p ^ k, pow_mem hp k, by rw [map_pow, h3]⟩)
    fun k => ⟨p⁻¹ ^ k, pow_mem (inv_mem hp) k, map_pow _ _ _⟩
  rw [mem_stabArch, ← hm]
  change Formalism.UG.cT _ (m g).1 * 1 * (m g).1 = 1
  rw [mul_one, ← h2]
  exact Matrix.map_injective (infEmb_bijective h τ).1 (h4.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)

theorem exists_isMaxCpt (h : IsCMExt F E σ) (hJ : IsHermND σ J) : ∃ K, IsMaxCpt σ J K := by
  choose c ε hc using Frames.exists_arch_frame h hJ
  exact ⟨_, isMaxCpt_majCpt h fun w => ⟨ε w, hc w⟩⟩

example (ξ : E) (hξ : σ ξ = -ξ) : ∃ g ∈ ratPts σ !![0, 1; 1, 0] ⊓
    unipFlag σ !![0, 1; 1, 0] (!![1; 0] : Matrix (Fin 2) (Fin 1) E) fun _ => 0,
      (matHom _ σ _ g).1 = adMat F !![1, ξ; 0, 1] := by
  let γ : GRat σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) := ⟨⟨!![1, ξ; 0, 1], !![1, -ξ; 0, 1], by simp [one_fin_two],
    by simp [one_fin_two]⟩, show _ * _ * _ = _ by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.UG.cT, Matrix.mul_apply, Fin.sum_univ_two, hξ]⟩
  have e : (matHom _ σ _ (ratEmb σ _ γ)).1 = adMat F !![1, ξ; 0, 1] := rfl
  refine ⟨ratEmb σ _ γ, ⟨range_ratEmb σ _ ▸ ⟨γ, rfl⟩, Subgroup.subset_closure ⟨fun i => ⟨0, fun _ _ => rfl, ?_⟩,
    fun x _ => ⟨fun _ => inclR (AF F) (ξ * x 1), ?_⟩⟩⟩, e⟩ <;> rw [e] <;> funext k <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subsingleton.elim _ (0 : Fin 1)]

omit [NumberField E] in

theorem isConstTerm_iff : IsConstTerm σ J C φ c ↔ IsConstTermOn σ J (unipRad σ J C) φ c := Iff.rfl

theorem isConstTerm_iff_unipFlag : IsConstTerm σ J C φ c ↔ IsConstTermOn σ J (unipFlag σ J C fun _ => 0) φ c := by
  rw [unipFlag_const]; rfl

omit [NumberField E] in

theorem isConstTermOn_const (N : Subgroup (GAd σ J)) (a : ℂ) : IsConstTermOn σ J N (fun _ => a) fun _ => a :=
  fun μ 𝓕 _ _ h _ => by simp [Measure.real, h]

theorem isConstTermOn_constTermOn [LocallyCompactSpace N] (hφ : LeftInv (ratPts σ J ⊓ N) φ) :
    IsConstTermOn σ J N φ (constTermOn (ratPts σ J) N φ) := fun μ 𝓕 _ h h1 g => by
  have hl : LeftInv ((ratPts σ J).subgroupOf N) fun u : N => φ (u * g) := fun γ hγ u => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hφ _ ⟨hγ, γ.2⟩ _
  rw [constTermOn, GlobalTheory.Cusp.probMeasure_eq μ, integral_smul_measure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h, h1, inv_one, ENNReal.toReal_one, one_smul]
  exact integral_congr_ae (.of_forall hl.descend_mk)

theorem exists_mass_one [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) : ∃ (μ : Measure N) (𝓕 : Set N),
    μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf N) 𝓕 μ ∧ μ 𝓕 = 1 := by
  have h := isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf N) (Measure.haar : Measure N)
  have h0 := h.measure_ne_zero (NeZero.ne _)
  have h1 := hc.measure_ne_top h
  exact ⟨(Measure.haar (stdDom ((ratPts σ J).subgroupOf N)))⁻¹ • Measure.haar, _,
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
    h.mono Measure.smul_absolutelyContinuous, by simp [ENNReal.inv_mul_cancel h0 h1]⟩

theorem IsConstTermOn.unique [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) (h : IsConstTermOn σ J N φ c)
    (h' : IsConstTermOn σ J N φ c') : c = c' :=
  let ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
  funext fun g => (h μ 𝓕 h1 h2 h3 g).trans (h' μ 𝓕 h1 h2 h3 g).symm

theorem isConstTermOn_iff [LocallyCompactSpace N] (hc : Cocompact (ratPts σ J) N) (hφ : LeftInv (ratPts σ J ⊓ N) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J) N φ :=
  ⟨fun h => h.unique hc (isConstTermOn_constTermOn hφ), fun h => h ▸ isConstTermOn_constTermOn hφ⟩

instance discreteTopology_ratPts_inf (P : Subgroup (GAd σ J)) : DiscreteTopology (ratPts σ J ⊓ P : Subgroup (GAd σ J)) :=
  .of_continuous_injective (f := Subgroup.inclusion (inf_le_left : ratPts σ J ⊓ P ≤ ratPts σ J))
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

section Flag

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hC : IsIsoCols σ J C)
include h hJ hC

theorem existsUnique_isConstTermOn (d : Fin r → ℕ) (hφ : LeftInv (ratPts σ J ⊓ unipFlag σ J C d) φ) :
    ∃! c, IsConstTermOn σ J (unipFlag σ J C d) φ c :=
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  ⟨_, isConstTermOn_constTermOn hφ, fun _ hc =>
    (isConstTermOn_iff (cocompact_unipFlag hJ (sigma_sigma h) hC d) hφ).1 hc⟩

theorem locallyCompact_unipRad : LocallyCompactSpace (unipRad σ J C) :=
  unipFlag_const (σ := σ) (J := J) C 0 ▸ locallyCompact_unipFlag hJ (sigma_sigma h) hC _

theorem cocompact_unipRad : Cocompact (ratPts σ J) (unipRad σ J C) :=
  unipFlag_const (σ := σ) (J := J) C 0 ▸ cocompact_unipFlag hJ (sigma_sigma h) hC _

theorem existsUnique_isConstTerm (hφ : LeftInv (ratPts σ J) φ) : ∃! c, IsConstTerm σ J C φ c := by
  simp only [isConstTerm_iff_unipFlag]
  exact existsUnique_isConstTermOn h hJ hC _ fun γ hγ => hφ γ hγ.1

theorem IsConstTermOn.eq_constTermOn_par {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) [LocallyCompactSpace (unipFlag σ J C d)] :
    Cocompact (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) ∧
      c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) φ := by
  have hco := cocompact_unipFlag hJ (sigma_sigma h) hC d
  have e : (ratPts σ J ⊓ parFlag σ J C d).subgroupOf (unipFlag σ J C d) = (ratPts σ J).subgroupOf (unipFlag σ J C d) :=
    Subgroup.ext fun u => and_iff_left (unipFlag_le_parFlag hJ (sigma_sigma h) hC d u.2)
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hco
  refine ⟨by rw [Cocompact, e]; exact hco, funext fun g => (hc μ 𝓕 h1 h2 h3 g).trans ?_⟩
  exact (GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g).symm

theorem IsConstTermOn.leftInv {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) : LeftInv (leftGrp σ J C d) c := by
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφ
  let S : Subgroup (GAd σ J) := MulAction.stabilizer (GAd σ J)ᵈᵐᵃ c |>.comap ((MulEquiv.inv' (GAd σ J)).toMonoidHom)
  have hS : ∀ γ, γ ∈ S ↔ ∀ g, c (γ⁻¹ * g) = c g := fun γ => funext_iff
  have : leftGrp σ J C d ≤ S := sup_le (fun u hu => (hS u).2 (e ▸ hco.constTermOn_mul_left hφ (inv_mem hu)))
    fun γ hγ => (hS γ).2 (e ▸ GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hφ (inv_mem hγ) fun u =>
      ⟨conj_mem_unipFlag hJ (sigma_sigma h) hC d (inv_mem hγ.2), fun hu => by
        simpa [mul_assoc] using conj_mem_unipFlag hJ (sigma_sigma h) hC d hγ.2 hu⟩)
  exact fun γ hγ g => by simpa using (hS _).1 (this (inv_mem hγ)) g

theorem IsConstTermOn.continuous {d : Fin r → ℕ} (hc : IsConstTermOn σ J (unipFlag σ J C d) φ c)
    (hφ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ) (hφc : Continuous φ) : Continuous c := by
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφ
  exact e ▸ hco.continuous_constTermOn hφ hφc

end Flag

omit [NumberField F] [NumberField E] in

theorem isIsoCols_of_isWittFrame {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) (hσ : ∀ x, σ (σ x) = x)
    (hJ : IsHermND σ J) {k : ℕ} (hk : k ≤ r) : IsIsoCols σ J (X.submatrix id (Fin.castLE hk)) := by
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => hσ _, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have hX : LinearIndependent E Xᵀ := Matrix.mulVec_injective_iff.1 fun a b e => by
    simpa only [Matrix.mulVec_mulVec, yx, Matrix.one_mulVec] using congrArg ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ ·) e
  exact ⟨hX.comp _ (Fin.castLE_injective hk), Matrix.ext fun i j => congrFun (congrFun hW.xx _) _⟩

example (h : IsCMExt F E σ) (a : ℂ) (c : GAd σ !![0, 1; 1, 0] → ℂ) :
    IsConstTerm σ !![0, 1; 1, 0] ((!![1; 0] : Matrix (Fin 2) (Fin 1) E).submatrix id (Fin.castLE le_rfl)) (fun _ => a) c ↔
      c = fun _ => a := by
  have hJ : IsHermND σ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) :=
    ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp⟩
  exact ⟨fun hc => (existsUnique_isConstTerm h hJ (isIsoCols_of_isWittFrame isWittFrame_plane (sigma_sigma h) hJ le_rfl)
    fun _ _ _ => rfl).unique hc (isConstTermOn_const _ a), fun e => e ▸ isConstTermOn_const _ a⟩

example : ∃ (μ : Measure (GAd σ J)) (𝓕 : Set (GAd σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratPts σ J) 𝓕 μ :=
  ⟨Measure.haar, _, inferInstance, isFundamentalDomain_stdDom _ _⟩

end GlobalTheory.UAut

end
end
