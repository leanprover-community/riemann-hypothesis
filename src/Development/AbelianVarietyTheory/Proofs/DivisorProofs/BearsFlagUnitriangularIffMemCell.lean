import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentTriangularFactor

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagLU

theorem det_lead {K : Type} [CommRing K] {s : ℕ} (g : Matrix (Fin s) (Fin s) K) (l : ℕ) (hl : l ≤ s) :
    (g.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
  let e : Fin l ≃ {a : Fin s // (a : ℕ) < l} :=
    { toFun := fun i => ⟨Fin.castLE hl i, i.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem exists_lu_subring : ∀ (K : Type) [Field K] (O : Subring K) (s : ℕ) (g : Matrix (Fin s) (Fin s) K), (∀ i j, g i j ∈ O) → (∀ k : ℕ, (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 ∧ ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det)⁻¹ ∈ O) → ∃ (y : Low s → K) (b : Matrix (Fin s) (Fin s) K), (∀ j, y j ∈ O) ∧ (∀ i j, b i j ∈ O) ∧ (∀ i j, i < j → b i j = 0) ∧ g = b * upU y := by
  intro K _ O s g hg hmin
  let A : Matrix (Fin s) (Fin s) O := Matrix.of fun i j => ⟨g j i, hg j i⟩
  have hA : A.map O.subtype = gᵀ := by ext i j; rfl
  have hu : ∀ l : Fin (s + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    have h1 : ((A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det : K) =
        (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
      have h2 := det_lead g l l.is_le
      rw [← O.coe_subtype, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA,
        ← Matrix.transpose_submatrix, Matrix.det_transpose, h2]
    obtain ⟨h0, hi⟩ := hmin l
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, h1]
    exact mul_inv_cancel₀ h0
  obtain ⟨n, M, hM, -, hAe⟩ := GlobalTheory.FlagCell.exists_lu O s A hu
  refine ⟨fun j => n j, (M.map O.subtype)ᵀ, fun j => (n j).2, fun i j => (M j i).2, ?_, ?_⟩
  · intro i j hij
    show ((M j i : O) : K) = 0
    rw [hM (i := j) (j := i) hij]; rfl
  · have key : A.map O.subtype = (GlobalTheory.FlagCell.uniR n * M).map O.subtype := by rw [← hAe]
    rw [hA, Matrix.map_mul, GlobalTheory.FlagCell.map_uniR] at key
    have h3 : (upU fun j => (n j : K)) = (GlobalTheory.FlagCell.uniR fun j => O.subtype (n j))ᵀ := by
      ext a b
      simp only [upU, Matrix.of_apply, Matrix.transpose_apply, GlobalTheory.FlagCell.uniR_apply, eq_comm]
      rfl
    rw [h3, ← Matrix.transpose_mul, ← key, Matrix.transpose_transpose]

end GlobalTheory.FlagLU
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem lowMul_upU_leadMinor_ne_zero (K : Type) [Field K] (s : ℕ) (y : Low s → K) (b : Matrix (Fin s) (Fin s) K) (hb : ∀ i j, i < j → b i j = 0) (hdet : b.det ≠ 0) :
    (upU y).det = 1 ∧ ∀ k : ℕ, ((b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 := by
  have hU : ∀ a c : Fin s, c < a → upU y a c = 0 := by
    intro a c h
    simp [upU, Matrix.of_apply, not_lt.mpr h.le, h.ne']
  have hUd : ∀ a : Fin s, upU y a a = 1 := by
    intro a; simp [upU, Matrix.of_apply]
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h1 : b.det = ∏ i, b i i := Matrix.det_of_lowerTriangular b (fun i j h => hb i j h)
    rw [h1] at hdet
    intro i
    exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular (fun a c h => hU a c h)]
    simp [hUd]
  · intro k
    have hmul : (b * upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
          (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) =
        b.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) *
          (upU y).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s)
            (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < k)]
      have h0 : ∑ l : {a : Fin s // ¬ (a : ℕ) < k}, b i.1 l.1 * upU y l.1 j.1 = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        have : i.1 < l.1 := by
          have := i.2; have := l.2; rw [Fin.lt_iff_val_lt_val]; omega
        rw [hb _ _ this, zero_mul]
      rw [h0, add_zero]
    rw [hmul, Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => hb i.1 j.1 h)]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i.1)
    · rw [Matrix.det_of_upperTriangular (fun i j h => hU i.1 j.1 h)]
      simp [hUd]

end GlobalTheory.FlagCell2
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_unique_of_lower : ∀ (K : Type) [Field K] (s : ℕ) (y y' : Low s → K) (b : Matrix (Fin s) (Fin s) K),
    (∀ i j, i < j → b i j = 0) → upU y = b * upU y' → y = y' := by
  intro K _ s y y' b hb h
  have key : ∀ i j : Fin s, (∀ k, k < j → b i k = 0) → upU y i j = b i j := by
    intro i j hk
    rw [h, Matrix.mul_apply, Finset.sum_eq_single j]
    · simp [upU]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h1 | h1
      · rw [hk k h1, zero_mul]
      · simp [upU, not_lt.mpr h1.le, hkj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have low : ∀ (i : Fin s) (N : ℕ) (j : Fin s), j.1 < N → j < i → b i j = 0 := by
    intro i N
    induction N with
    | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ N ih =>
      intro j hj hji
      rw [← key i j fun k hk => ih k (by have := Fin.lt_def.mp hk; omega) (hk.trans hji)]
      simp [upU, not_lt.mpr hji.le, hji.ne']
  have hb1 : b = 1 := by
    ext i j
    rcases lt_trichotomy i j with h1 | rfl | h1
    · rw [hb i j h1, Matrix.one_apply_ne h1.ne]
    · rw [← key i i fun k hk => low i (k.1 + 1) k (Nat.lt_succ_self _) hk]
      simp [upU]
    · rw [low i (j.1 + 1) j (Nat.lt_succ_self _) h1, Matrix.one_apply_ne h1.ne']
  rw [hb1, Matrix.one_mul] at h
  funext ⟨⟨c, a⟩, hac⟩
  have hac' : a < c := hac
  have := congrFun (congrFun h a) c
  simpa [upU, hac'] using this

end GlobalTheory.FlagCell2
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.BearsCell

variable {ι : Type} {m : ι → ℕ}

theorem upM_map {K K' : Type} [Field K] [Field K'] (v : K → K') (h0 : v 0 = 0) (h1 : v 1 = 1) (u : Cell m → K) :
    (upM u).map v = upM fun j => v (u j) := by
  funext τ
  ext a b
  simp only [Mat.map, upM, upU, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp [h0, h1]

theorem det_upM {K : Type} [Field K] (u : Cell m → K) (τ : ι) : (upM u τ).det = 1 :=
  (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K (m τ) _ 1 (fun _ _ h => Matrix.one_apply_ne h.ne) (by simp)).1

theorem exists_lu {K K' : Type} [Field K] [Field K'] {O : Subring K} (v : K → K') (ψ : O →+* K')
    (hv : ∀ x : O, v x = ψ x) (hu : ∀ x : O, ψ x ≠ 0 → (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ O) {g : Mat m K} (hg : Par 0 O g)
    {y₀ : Cell m → K'} (hP : Par m ⊤ (upM y₀ * (g.map v)⁻¹)) :
    ∃ (u : Cell m → K) (b : Mat m K), Par m O b ∧ g = b * upM u ∧ ∀ j, v (u j) = y₀ j := by
  have hgv := hg.map_of v ψ hv
  have hy : ∀ τ, (upM y₀ τ).det ≠ 0 := fun τ => (det_upM y₀ τ).trans_ne one_ne_zero
  have e : g.map v = (upM y₀ * (g.map v)⁻¹)⁻¹ * upM y₀ := by
    rw [Mat.mul_inv_rev, Mat.inv_inv hgv.det_ne, mul_assoc, Mat.inv_mul hy, mul_one]
  have hmin : ∀ τ (k : ℕ), ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det ≠ 0 ∧
      (((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det)⁻¹ ∈ O := fun τ k => by
    let N : Matrix {a : Fin (m τ) // (a : ℕ) < k} {a : Fin (m τ) // (a : ℕ) < k} O := fun a b => ⟨_, (hg τ).1 a.1 b.1⟩
    have e1 : (N.det : K) = ((g τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val).det :=
      O.subtype.map_det N
    have e2 : ψ.mapMatrix N =
        (g.map v τ).submatrix (Subtype.val : {a : Fin (m τ) // (a : ℕ) < k} → Fin (m τ)) Subtype.val := by
      ext a b
      exact (hv (N a b)).symm
    rw [← e1]
    refine hu _ ?_
    rw [ψ.map_det, e2, e]
    exact (GlobalTheory.FlagCell2.lowMul_upU_leadMinor_ne_zero K' (m τ) _ _ (fun i j h => (hP.inv τ).2.2.2 i j i.2 h) (hP.inv.det_ne τ)).2 k
  choose y b h1 h2 h3 h4 using fun τ => GlobalTheory.FlagLU.exists_lu_subring K O (m τ) (g τ) (hg τ).1 (hmin τ)
  have hgb : g = b * upM (fun j : Cell m => y j.1 j.2) := funext h4
  have hd : ∀ τ, (b τ).det = (g τ).det := fun τ => by
    rw [hgb, Pi.mul_apply, Matrix.det_mul, det_upM, mul_one]
  have hb : Par m O b := fun τ => ⟨h2 τ, hd τ ▸ (hg τ).2.1, hd τ ▸ (hg τ).2.2.1, fun i j _ h => h3 τ i j h⟩
  have hU : Par 0 O (upM fun j : Cell m => y j.1 j.2) := by
    have := (hb.inv.mono (k' := 0) (fun _ => Nat.zero_le _) le_rfl).mul hg
    rwa [hgb, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul] at this
  refine ⟨_, b, hb, hgb, fun j => ?_⟩
  have e3 : g.map v = Mat.map b v * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [← upM_map v ((hv 0).trans (map_zero ψ)) ((hv 1).trans (map_one ψ)), ← Par.map_mul_of hb hU v ψ hv, ← hgb]
  have e4 : upM y₀ = (upM y₀ * (g.map v)⁻¹ * Mat.map b v) * upM fun j : Cell m => v (y j.1 j.2) := by
    rw [mul_assoc, ← e3, mul_assoc, Mat.inv_mul hgv.det_ne, mul_one]
  have hc := hP.mul (hb.map_of v ψ hv)
  exact (congrFun (GlobalTheory.FlagCell2.upU_unique_of_lower K' (m j.1) _ _ _ (fun i k h => (hc j.1).2.2.2 i k i.2 h) (congrFun e4 j.1)) j.2).symm

theorem bears_iff : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hf A K _ p hA y₀
  have hd : ∀ σ, (A.map φ σ).det ≠ 0 := fun σ =>
    (Mat.det_map A (φ : X.Fn →+* Y.Fn) σ).trans_ne ((map_ne_zero _).2 (Fr.det_ne hA σ))
  have hr := GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf Y) p (IsLocalRing.closedPoint K)
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨u, b, hb, hg, hu⟩ := exists_lu ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.valHom (M := ratOf Y) p _ hr)
      (fun _ => rfl) (fun x hx => (GlobalTheory.ZH.RatModel.isUnit_O_iff x).1
        ((GlobalTheory.ZH.RatModel.val_ne_zero_iff (M := ratOf Y) hr x).1 hx)) (hf.sub _ A' hA' A hA) hP
    refine ⟨u, (Fr.mem_iff hA').2 ?_, hu⟩
    have e : upM u * A.map φ * A'⁻¹ = b⁻¹ := by
      have e1 : upM u = b⁻¹ * (A' * (A.map φ)⁻¹) := by
        rw [hg, ← mul_assoc, Mat.inv_mul hb.det_ne, one_mul]
      rw [e1, mul_assoc b⁻¹, mul_assoc A', Mat.inv_mul hd, mul_one, mul_assoc, Mat.mul_inv (Fr.det_ne hA'), mul_one]
    rw [e]
    exact hb.inv
  · rintro ⟨u, hu, hy⟩
    refine ⟨_, hu, ?_⟩
    rw [mul_assoc, Mat.mul_inv hd, mul_one,
      upM_map ((ratOf Y).val p) (GlobalTheory.ZH.RatModel.val_zero (M := ratOf Y) p)
        (GlobalTheory.ZH.RatModel.val_one (M := ratOf Y) p), show (fun j => (ratOf Y).val p (u j)) = y₀ from funext hy,
      Mat.mul_inv fun τ => (det_upM y₀ τ).trans_ne one_ne_zero]
    exact Par.one

end GlobalTheory.FlagCell2.BearsCell
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (K : Type) [Field K] (p : Sp K ⟶ Y.X), A ∈ E.S (f (p (IsLocalRing.closedPoint K))) → ∀ y₀ : Cell m → K, Bears E' φ A (upM y₀) p ↔ ∃ u : Cell m → Y.Fn, upM u * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  atlas_forward_decl GlobalTheory.FlagCell2.BearsCell.bears_iff
end
