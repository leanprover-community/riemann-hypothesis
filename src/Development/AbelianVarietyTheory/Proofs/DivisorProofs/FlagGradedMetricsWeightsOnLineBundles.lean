import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.FlagChange

theorem diag_unitAt_and_mul : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  intro F _ X ι m E B hB z A A' hA hA' x
  obtain ⟨τ, i⟩ := x
  have hP : Par m ((ratOf X).O z).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have hl : ∀ (C : Mat m X.Fn) (O : Subring X.Fn), Par m O C → (C τ).BlockTriangular OrderDual.toDual := by
    intro C O hC a b hab
    exact (hC τ).2.2.2 a b a.2 hab
  refine ⟨?_, ?_⟩
  · set P := A' * A⁻¹ with hPdef
    have hdet : (P τ).det = P τ i i * ∏ j ∈ Finset.univ.erase i, P τ j j := by
      rw [Matrix.det_of_lowerTriangular _ (hl P _ hP),
        Finset.mul_prod_erase Finset.univ (fun j => P τ j j) (Finset.mem_univ i)]
    have hne : (P τ).det ≠ 0 := hP.det_ne τ
    rw [hdet] at hne
    have hii : P τ i i ≠ 0 := left_ne_zero_of_mul hne
    have hR : ∏ j ∈ Finset.univ.erase i, P τ j j ≠ 0 := right_ne_zero_of_mul hne
    have hmem : ∀ a b, P τ a b ∈ (ratOf X).O z := fun a b => (hP τ).1 a b
    have hinv : (P τ i i)⁻¹ ∈ (ratOf X).O z := by
      have e : (P τ i i)⁻¹ = (P τ).det⁻¹ * ∏ j ∈ Finset.univ.erase i, P τ j j := by
        rw [hdet, _root_.mul_inv, mul_assoc, inv_mul_cancel₀ hR, mul_one]
      rw [e]
      refine ((ratOf X).O z).mul_mem (hP τ).2.2.1 (((ratOf X).O z).prod_mem fun j _ => hmem j j)
    exact (unitAt_iff hii).2 ⟨mem_O_ratOf.1 (hmem i i), mem_O_ratOf.1 hinv⟩
  · have hA'g : A' ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA'
    have hQ : Par m ((ratOf X).O (genericPoint X.X)).toSubring (B * A'⁻¹) := (Fr.mem_iff hA'g).1 hB
    have e : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
      rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
    rw [e]
    show ((B * A'⁻¹) τ * (A' * A⁻¹) τ) i i = _
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun l _ hl' => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [(hP τ).2.2.2 l i l.2 h, mul_zero]
    · rw [(hQ τ).2.2.2 i l i.2 h, zero_mul]

end GlobalTheory.FlagChange
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  atlas_forward_decl GlobalTheory.FlagChange.diag_unitAt_and_mul
end

section
namespace GlobalTheory.DiagonalTimesLowerTriangular

theorem diag_mul_of_lower {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by
  intro i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem main : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i :=
  fun ha hb => diag_mul_of_lower ha hb

end GlobalTheory.DiagonalTimesLowerTriangular
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.ChernCalc
open scoped Matrix ComplexOrder

namespace GlobalTheory.LeadingMinorPositivity

section Lin

variable {s : ℕ}

theorem submatrix_mul_lower {κ : Type} (T : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0)
    (M : Matrix (Fin s) κ ℂ) (j : ℕ) :
    (T * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id =
      T.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id := by
  ext a b
  change ∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp)
    (fun l => T a l * M l b)]
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra h
  refine hl ?_
  rw [hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]

theorem leadMinor_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (j : ℕ) :
    leadMinor (T * G * Tᴴ) j =
      ((∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < j, ‖T a a‖ ^ 2 : ℝ) : ℂ) * leadMinor G j := by
  let v : {a : Fin s // (a : ℕ) < j} → Fin s := Subtype.val
  have h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ := by
    have := submatrix_mul_lower T hT (G.submatrix v id)ᴴ j
    have h2 := (congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)
    refine Eq.trans ?_ (h2.trans ?_)
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rfl
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
      rfl
  have h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ) := by
    have := submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j
    rw [← h1, Matrix.mul_assoc]
    exact this
  have h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a) :=
    Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab
  unfold leadMinor
  change ((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4,
    Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]
  congr 1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

theorem leadMinor_re_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re :=
  (Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1

theorem grD_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (i : Fin s) : 0 < grD G i :=
  div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)

theorem grD_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (hd : ∀ a, T a a ≠ 0) (i : Fin s) :
    grD (T * G * Tᴴ) i = ‖T i i‖ ^ 2 * grD G i := by
  have e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))
  rw [grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e,
    Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]

theorem diag_mul_lower {K : Type} [Field K] (S T : Matrix (Fin s) (Fin s) K) (hS : ∀ a b, a < b → S a b = 0)
    (hT : ∀ a b, a < b → T a b = 0) (i : Fin s) : (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hT l i h, mul_zero]
  · rw [hS i l h, zero_mul]

end Lin

theorem green_frame_indep (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H)
    (B : Mat m X.Fn) (hB : B ∈ E.S (genericPoint X.X)) (y : GlobalTheory.CxPts X.str σ)
    (A : Mat m X.Fn) (hA : A ∈ E.S (under y)) (A' : Mat m X.Fn) (hA' : A' ∈ E.S (under y))
    (x : Root m) (f : X.Fn) (hu : UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f)) :
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
      -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  obtain ⟨τ, i⟩ := x
  have hT := (Fr.mem_iff hA).1 hA'
  have hS := (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hV := hT.map_of (ratVal · y) ψ hψ τ
  have hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0 := fun a b h => hV.2.2.2 a b a.2 h
  have hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0 := by
    have h := hV.2.1
    rw [Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
    rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
  have e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i := by
    rw [e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h)
      (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]
  have hu0 := ratVal_ne_zero hu
  have hur : RegAt (under y) ((B * A'⁻¹) τ i i / f) := by
    by_contra h
    exact hu0 (dif_neg h)
  have ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0 := hd i
  have hg := (grD_pos (hH.posDef y A hA τ) i).ne'
  have e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i := by
    rw [hH.trans y A hA A' hA' τ]
    exact grD_conj _ _ hlow hd i
  have n1 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
  have n2 := pow_ne_zero 2 (norm_ne_zero_iff.2 ht)
  dsimp only at n1 ⊢
  rw [e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2,
    Real.log_mul n2 hg]
  ring

end GlobalTheory.LeadingMinorPositivity
end
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem grWeight_frame_indep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first
  | exact @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | (apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep ..)

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  atlas_forward_decl GlobalTheory.ChernCalc.grWeight_frame_indep
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem cInfAt_ratVal_on {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {κ : Type} [Fintype κ] {f : κ → X.Fn}
    {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a)) {G : (κ → ℂ) → ℝ} {O : Set (κ → ℂ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) (hy : (fun a => ratVal (f a) y) ∈ O) :
    CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hyU g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hyU)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  have hev (z : CxPts X.str σ) (hz : z ∈ ptsIn X.str σ W) :
      (fun a => ev X.str σ W (resG X.X (hle a) (g a)) z) = fun a => ratVal (f a) z := by
    funext a
    rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, O, hW, hO, ?_, hG, ?_⟩
  · rw [hev y hW]; exact hy
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
    rw [hev z hz]

theorem cInfAt_neg_log_normSq_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : CxPts X.str σ} {u : X.Fn}
    (hu : UnitAt (under y) u) : CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2)) y := by
  have hO : IsOpen {w : Unit → ℂ | w () ≠ 0} := isOpen_ne_fun (continuous_apply ()) continuous_const
  have hG : ContDiffOn ℝ ∞ (fun w : Unit → ℂ => -Real.log (‖w ()‖ ^ 2)) {w | w () ≠ 0} := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun w : Unit → ℂ => ‖w ()‖ ^ 2) w :=
      ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffAt
    have h2 : ‖w ()‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
    exact (h1.log h2).neg.contDiffWithinAt
  exact cInfAt_ratVal_on (κ := Unit) (f := fun _ => u) (fun _ => hu.regAt) hO hG (ratVal_ne_zero hu)

end GlobalTheory.ChernCalc

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChernCalc.cInfAt_logUnit_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i
  refine (GlobalTheory.ChernCalc.cInfAt_neg_log_normSq_ratVal hu).add ?_ |>.congr (Eventually.of_forall fun z => sub_eq_add_neg _ _)
  have := X.smooth_str
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hc)
  obtain ⟨O, hOP, hOo, hyO⟩ := eventually_nhds_iff.1 hev
  have hS : IsOpen (c.e.source ∩ c.e ⁻¹' O) := c.e.isOpen_inter_preimage hOo
  refine cInfAt_of_chart hS c ?_ hc ⟨hc, hyO⟩
  intro v hv
  have hvO : v ∈ O := by
    have := hv.2.2
    rwa [Set.mem_preimage, c.e.right_inv hv.1] at this
  obtain ⟨hsm, hpd⟩ := hOP v hvO
  have hd := (ldPart_grD_smooth _ _ _ v hsm hpd).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 i).1
  exact (hd.log hpos.ne').neg.contDiffWithinAt
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  atlas_forward_decl GlobalTheory.ChernCalc.cInfAt_logUnit_grD
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leviForm_neg_log_unit_sub_log_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i c hy
  obtain ⟨W, hW, a, rfl⟩ := hu.regAt.exists_fnOf
  have hyW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 hW
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hm := ChartGlue.mem_over c.e hy hyW
  have hg := c.holo W a
  have hf : ContDiffAt ℂ 2 (ev X.str σ W a ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev X.str σ W a ∘ c.e.symm) (c.e y) ≠ 0 := by
    have := ratVal_ne_zero hu
    rw [ratVal_fnOf hyW] at this
    simpa [Function.comp, c.e.left_inv hy] using this
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hy).self_of_nhds
  have hG := (ldPart_grD_smooth _ _ _ _ hsm.1 hsm.2).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hsm.2).2.1 i).1
  have hD : ContDiffAt ℝ 2 (fun v => Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) :=
    (hG.log hpos.ne').of_le (WithTop.coe_le_coe.2 le_top)
  rw [leviForm_congr (u' := fun v => -Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2) +
      -Real.log (grD (H A (c.e.symm v) τ) i)), leviForm_add hlog.neg hD.neg,
    leviForm_neg (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)), leviForm_log_normSq_eq_zero hf h0,
    neg_zero, zero_add]
  filter_upwards [ho.mem_nhds hm] with v hv
  simp only [Function.comp, sub_eq_add_neg]
  rw [ratVal_fnOf hv.2]

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  atlas_forward_decl GlobalTheory.ChernCalc.leviForm_neg_log_unit_sub_log_grD
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem graded_weight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr →
    IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L),
      Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  intro F _ σ X ι _ m E H gr hG hH x
  obtain ⟨B, hB, hgr⟩ := hG
  have hunit : ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∀ f : X.Fnˣ, (gr x).IsEqn z f →
      UnitAt z ((B * A⁻¹) x.1 x.2 x.2 / f) := by
    intro z A hA f hf
    obtain ⟨A₀, hA₀, t, ht, he⟩ := hgr z x
    obtain ⟨hu, hd⟩ := GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units F X ι m E B hB z A₀ A hA₀ hA x
    have htf : UnitAt z ((t : X.Fn) / f) := (hf.iff_unitAt).1 he
    have hne : (A * A₀⁻¹) x.1 x.2 x.2 ≠ 0 := fun h0 => by
      obtain ⟨a, ha, h⟩ := hu
      rw [h0] at h
      exact (ha.map (algebraMap _ X.Fn)).ne_zero h
    have e : (B * A⁻¹) x.1 x.2 x.2 / f = ((t : X.Fn) / f) * ((A * A₀⁻¹) x.1 x.2 x.2)⁻¹ := by
      rw [← ht, hd]; field_simp
    rw [e]; exact htf.mul hu.inv

  let Ach : CxPts X.str σ → Mat m X.Fn := fun y => (E.nonempty (under y)).choose
  have hAch : ∀ y, Ach y ∈ E.S (under y) := fun y => (E.nonempty (under y)).choose_spec
  let val : Mat m X.Fn → CxPts X.str σ → X.Fn → ℝ := fun A y f =>
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2)
  let D := gr x
  have hP := presents_toLB D
  have heq : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      D.IsEqn (under y) (i.1.2) := fun i y hy => i.2.2 _ (mem_ptsIn.1 hy)
  have hindep : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      ∀ A ∈ E.S (under y), val (Ach y) y i.1.2 = val A y i.1.2 := fun i y hy A hA =>
    GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent F σ X ι m E H hH B hB y (Ach y) (hAch y) A hA x _ (hunit _ A hA _ (heq i y hy))
  let ψ : Weight X.str σ (toLB D) :=
    { isLB := isLB_toLB D
      φ := fun i y => val (Ach y) y i.1.2
      trans := by
        intro i j y hi hj
        have hu1 := hunit _ _ (hAch y) _ (heq i y hi)
        have hu2 : UnitAt (under y) ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := ((heq j y hj).iff_unitAt).1 (heq i y hi)
        have hg : gv X.str σ (toLB D) i j y = ratVal ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) y := by
          have hgen : genericPoint X.X ∈ (toLB D).U i ⊓ (toLB D).U j := ⟨i.2.1, j.2.1⟩
          rw [← fnOf_toLB_g i j hgen, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩) hgen]
          rfl
        have hi0 := (i.1.2).ne_zero
        have hj0 := (j.1.2).ne_zero
        have e : (B * (Ach y)⁻¹) x.1 x.2 x.2 / (j.1.2 : X.Fn) =
            ((B * (Ach y)⁻¹) x.1 x.2 x.2 / i.1.2) * ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := by
          field_simp
        show val (Ach y) y j.1.2 = val (Ach y) y i.1.2 - _
        simp only [val]
        rw [e, ratVal_mul hu1.regAt hu2.regAt, log_normSq_mul (ratVal_ne_zero hu1) (ratVal_ne_zero hu2), hg]
        ring }
  refine ⟨toLB D, fun i => i.1.2, ψ, hP, ?_, ?_⟩
  · intro i y hy
    have hu := hunit _ _ (hAch y) _ (heq i y hy)
    refine (GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2).congr ?_
    filter_upwards [frame_eventually_near F σ X ι m m E y (Ach y) (hAch y), (isOpen_ptsIn _).mem_nhds hy] with z hz hzi
    exact hindep i z hzi (Ach y) hz
  · funext p
    obtain ⟨⟨c, y⟩, hy⟩ := p
    have hy' : y ∈ c.e.source := hy
    have ha : y ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) := mem_pick ψ.isLB y
    have hu := hunit _ _ (hAch y) _ (heq _ y ha)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧ Ach y ∈ E.S (under z) :=
      Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds ha) (frame_eventually_near F σ X ι m m E y (Ach y) (hAch y))
    have hnear' : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧
        Ach y ∈ E.S (under (c.e.symm v)) := by
      have hc := c.e.continuousAt_symm (c.e.map_source hy')
      rw [ContinuousAt, c.e.left_inv hy'] at hc
      exact hc.eventually hnear
    have key : leviForm (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y) := by
      rw [leviForm_congr (u' := fun v => val (Ach y) (c.e.symm v) (pick ψ.isLB y).1.2)]
      · exact GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2 c hy'
      · filter_upwards [hnear'] with v hv
        exact hindep _ _ hv.1 (Ach y) hv.2
    have e1 : c1W ψ ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y)) := rfl
    have e2 : grF E H x ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y)) := rfl
    rw [e1, e2]
    unfold HermFrame.ddc
    rw [key]

end GlobalTheory.ChernCalc
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr → IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L), Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  atlas_forward_decl GlobalTheory.ChernCalc.graded_weight
end
