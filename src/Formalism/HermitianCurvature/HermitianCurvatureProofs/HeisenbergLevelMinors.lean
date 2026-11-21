import Formalism.HermitianCurvature.HermitianCurvatureProofs.JDomBoundOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfJqSmoothOfNnMaj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}



lemma hb_eq : Hb k = castW (Hpk k 0) := by
  ext i j
  simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Matrix.diagonal_apply, Hpk]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i = Fin.last k
    · subst hl
      simp [Fin.last]
    · have hv : (i : ℕ) ≠ k := fun h => hl (Fin.ext (by simpa [Fin.last] using h))
      have hlt : (i : ℕ) < k + 1 := i.isLt
      simp [hl, hv]
      omega
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hij, Fin.ext_iff, hv]


def NNSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m → ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        B.gN ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN)

def Slice1 : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)

def SliceRegularityClauses : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O




end Formalism.FourierDecayAlt.P.JFxDs5
end
end

section
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMinor : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)

def NNVol : Prop :=
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      μ {x | gN (Matrix.of x : Mat k r) ≤ R} ≤ ENNReal.ofReal (C * R ^ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2))

variable {k r : ℕ}

lemma list_prod_le : ∀ (l : List ℝ) (b : ℝ), (∀ x ∈ l, 0 ≤ x ∧ x ≤ b) → 0 ≤ l.prod ∧ l.prod ≤ b ^ l.length
  | [], b, _ => by simp
  | x :: l, b, h => by
    obtain ⟨h1, h2⟩ := list_prod_le l b (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    rw [List.prod_cons, List.length_cons, pow_succ]
    refine ⟨mul_nonneg hx.1 h1, ?_⟩
    calc x * l.prod ≤ b * b ^ l.length := mul_le_mul hx.2 h2 h1 (le_trans hx.1 hx.2)
      _ = b ^ l.length * b := by ring

lemma norm_le_gN (M : Mat k r) : ‖M‖ ≤ gN M := by
  have hg : gN M = Real.sqrt (∑ i, ∑ j, Complex.normSq (M i j)) := rfl
  rw [hg, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖M i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = |‖M i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ _ := Real.abs_le_sqrt h2

lemma gN_unit {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)

lemma gN_conjT (M : Mat k r) : gN Mᴴ = gN M := by
  show Real.sqrt _ = Real.sqrt _
  congr 1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))

lemma gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

lemma uw_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h ∈ UWset k r z, gN h ≤ C := by
  obtain ⟨C, hC⟩ := (B2x3.compactW k r z hz hT).exists_bound_of_continuousOn B6.gN_continuous.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun h hh => ?_⟩
  have := hC h hh
  rw [Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) (le_trans this (le_max_left _ _))

lemma intN (hV : NNVol) {μ : Measure (Mt k r)} (hμ : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) {β : ℝ}
    (hβ : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < β) :
    Integrable (fun x : Mt k r => gN (Matrix.of x : Mat k r) ^ (-β)) μ := by
  obtain ⟨C, hC⟩ := hV k r μ hμ
  have hge : ∀ᵐ x ∂μ, 1 ≤ gN (Matrix.of x : Mat k r) := by
    filter_upwards [B6.haar_ae hμ] with x hx using BetaSesquilinearity.gN_ge_one (B6.Nset_sub k r hx)
  have hlin := NormBallVolumes.shellInt (Mt k r) μ (fun x => gN (Matrix.of x : Mat k r)) C _ β (NormBallVolumes.gN_meas k r) hge
    (by positivity) hC hβ
  refine ⟨((NormBallVolumes.gN_meas k r).pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.rpow_nonneg (B6.gN_nonneg _) _)]
  exact hlin

lemma letter_bound {s1 s2 X : Mat k r} {CW CI CN : ℝ} (hCI : 0 ≤ CI) (hCN : 0 ≤ CN)
    (hX : unitLie k r X) (hi : gN s2⁻¹ ≤ CI) (hw : gN s2 ≤ CW) (hN : gN s1⁻¹ ≤ CN * gN s1) :
    ‖(s1 * s2)⁻¹ * X * (s1 * s2)‖ ≤ CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN s1 ^ 2 := by
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  have hn : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := gN_unit hX.2
  have ha : gN (s2⁻¹ * s1⁻¹ * X) ≤ CI * (CN * gN s1) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc gN (s2⁻¹ * s1⁻¹ * X) ≤ gN (s2⁻¹ * s1⁻¹) * gN X := gN_mul_le_hermitian_curvature _ _
      _ ≤ (gN s2⁻¹ * gN s1⁻¹) * gN X := mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
      _ ≤ (CI * (CN * gN s1)) * ((2 * r + k + 1 : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul hi hN (h0 _) hCI) hn (h0 _)
            (mul_nonneg hCI (mul_nonneg hCN (h0 _)))
  have hb : gN (s1 * s2) ≤ gN s1 * CW :=
    (gN_mul_le_hermitian_curvature _ _).trans (mul_le_mul_of_nonneg_left hw (h0 _))
  rw [Matrix.mul_inv_rev]
  calc ‖s2⁻¹ * s1⁻¹ * X * (s1 * s2)‖ ≤ gN (s2⁻¹ * s1⁻¹ * X * (s1 * s2)) := norm_le_gN _
    _ ≤ gN (s2⁻¹ * s1⁻¹ * X) * gN (s1 * s2) := gN_mul_le_hermitian_curvature _ _
    _ ≤ (CI * (CN * gN s1) * ((2 * r + k + 1 : ℕ) : ℝ)) * (gN s1 * CW) :=
        mul_le_mul ha hb (h0 _)
          (mul_nonneg (mul_nonneg hCI (mul_nonneg hCN (h0 _))) (Nat.cast_nonneg _))
    _ = CI * CN * CW * ((2 * r + k + 1 : ℕ) : ℝ) * gN s1 ^ 2 := by ring


lemma split_bound {x a a' C β : ℝ} (e : ℕ) (hx : 1 ≤ x) (ha : 0 < a) (ha' : 0 < a') (hC : 0 < C)
    (hβ : 0 ≤ β) (h1 : a ≤ C * x ^ e) (h2 : a' ≤ C * x ^ e) :
    x ^ (-(2 * (e : ℝ) * β)) ≤ C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by
  have hx0 : 0 < x := by linarith
  have hxe : 0 < x ^ e := pow_pos hx0 e
  have hCb : 0 < C ^ β := Real.rpow_pos_of_pos hC β
  have hxb : 0 < x ^ ((e : ℝ) * β) := Real.rpow_pos_of_pos hx0 _
  have one : ∀ b : ℝ, 0 < b → b ≤ C * x ^ e → x ^ (-((e : ℝ) * β)) ≤ C ^ β * b ^ (-β) := by
    intro b hb hbC
    have h := Real.rpow_le_rpow hb.le hbC hβ
    rw [Real.mul_rpow hC.le hxe.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le] at h
    have hbb : 0 < b ^ β := Real.rpow_pos_of_pos hb β
    have key : 1 / (C ^ β * x ^ ((e : ℝ) * β)) ≤ 1 / b ^ β := one_div_le_one_div_of_le hbb h
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hb.le]
    have e1 : (x ^ ((e : ℝ) * β))⁻¹ = C ^ β * (1 / (C ^ β * x ^ ((e : ℝ) * β))) := by
      field_simp
    rw [e1, ← one_div]
    exact mul_le_mul_of_nonneg_left key hCb.le
  have k1 := one a ha h1
  have k2 := one a' ha' h2
  have hsplit : x ^ (-(2 * (e : ℝ) * β)) = x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [hsplit]
  calc x ^ (-((e : ℝ) * β)) * x ^ (-((e : ℝ) * β))
      ≤ (C ^ β * a ^ (-β)) * (C ^ β * a' ^ (-β)) :=
        mul_le_mul k1 k2 (Real.rpow_nonneg hx0.le _)
          (mul_nonneg hCb.le (Real.rpow_nonneg ha.le _))
    _ = C ^ β * C ^ β * (a ^ (-β) * a' ^ (-β)) := by ring



section vol

open Formalism.FourierDecayAlt.P.B2x6

variable {k r' : ℕ}


lemma lev_bvec_iL (g : Mat k r') : ιLev k 1 r' g *ᵥ bvec (iL k r') = bvec (iL k r') := by
  have h0 : res (bvec (iL k r')) = 0 := funext fun j => Pi.single_eq_of_ne (lv_ne_iL j) _
  apply vext
  · rw [lev_mulVec_F]
  · rw [lev_mulVec_res, h0, Matrix.mulVec_zero]
  · rw [lev_mulVec_L]

lemma heisLev_col (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r') = x.1 j := by
  have h0 : res (bvec (iL k r')) = 0 := funext fun j => Pi.single_eq_of_ne (lv_ne_iL j) _
  have h1 : bvec (iL k r') (iL k r') = 1 := Pi.single_eq_same _ _
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r'), ← Matrix.mulVec_mulVec,
    lev_bvec_iL]
  calc (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) (lv k r' j)
      = res (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) j := rfl
    _ = (res (bvec (iL k r')) + bvec (iL k r') (iL k r') • x.1) j := by rw [heis_res]
    _ = x.1 j := by rw [h0, h1, one_smul, zero_add]

lemma heisLev_corner (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r')).im = x.2 := by
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r'), ← Matrix.mulVec_mulVec,
    lev_bvec_iL, ← ent]
  have h := B2x5.heis_col k r' x (iF k r')
  have e1 : Formalism.FourierDecayAlt.P.B2x6.iL k r' = Formalism.FourierDecayAlt.P.B2x5.iL k r' := rfl
  have e2 : Formalism.FourierDecayAlt.P.B2x6.iF k r' = Formalism.FourierDecayAlt.P.B2x5.i0 k r' := rfl
  rw [e1, h, e2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, B2x5.dual_base_vector_first_zero, B2x5.lifted_vector_first, B2x5.base_vector_first_one, zero_add, mul_one]
  simp [Formalism.FourierDecayAlt.B2.hb]

lemma sum_lv_le (f : Fin (2 * (1 + r') + k + 1) → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ j, f (lv k r' j) ≤ ∑ p, f p := by
  have hinj : Function.Injective (lv k r') := by
    intro a b h
    apply Fin.ext
    have h2 : (lv k r' a).val = (lv k r' b).val := congrArg Fin.val h
    have ea : (lv k r' a).val = a.val + 1 := rfl
    have eb : (lv k r' b).val = b.val + 1 := rfl
    omega
  calc ∑ j, f (lv k r' j) = ∑ p ∈ Finset.univ.map ⟨lv k r', hinj⟩, f p := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ p, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hf p)


lemma coord_le (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    ‖x‖ ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := by
  have hE : ∀ p q, ‖(Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q‖ ≤
      gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := fun p q =>
    (Matrix.norm_entry_le_entrywise_sup_norm _).trans (norm_le_gN _)
  have h0 : 0 ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := Real.sqrt_nonneg _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    rw [← heisLev_col x g j]
    exact hE _ _
  · rw [Real.norm_eq_abs, ← heisLev_corner x g]
    refine le_trans ?_ (hE (iF k r') (iL k r'))
    set z := (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r')
    have hz : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_nonneg z.re]
    calc |z.im| = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hz
      _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

end vol

def heisM (k r' : ℕ) (x : Formalism.FourierDecayAlt.B2.HPar k r') : Mt k (1 + r') := Formalism.FourierDecayAlt.B2.heis0 k r' x




def NNMinorL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)

lemma zhat_inv {g : Mat k r} (hg : g ∈ GV k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Zhat k r z' z g⁻¹ = (Zhat k r z z' g)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  unfold Zhat
  have hu := WeylGroupFacts.isUnit_of_uh hg
  calc herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z b) (fvec k r z' a)
      = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ fvec k r z b)) (g *ᵥ fvec k r z' a) := (B2x5.herm_UH _ hg _ _).symm
    _ = herm (Hpk k r) (fvec k r z b) (g *ᵥ fvec k r z' a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    _ = star (herm (Hpk k r) (g *ᵥ fvec k r z' a) (fvec k r z b)) :=
        (B2x4.herm_symm _ (B2x5.Hherm k r) _ _).symm

lemma dmin_inv {g : Mat k r} (hg : g ∈ GV k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Dmin k r z' z g⁻¹ l = star (Dmin k r z z' g l) := by
  simp only [Dmin]
  rw [zhat_inv hg z z', ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]









end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
end
end
