import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have hi := i.isLt
  show ∑ j, Hpk k r i j * v j = _
  split_ifs with h1 h2
  · simp_rw [hpk_out h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp_rw [hpk_mid h1]
    rw [Finset.sum_eq_single i]
    · simp [h2]
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp_rw [hpk_mid h1]
    rw [Finset.sum_eq_single i]
    · simp [h2]
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  split_ifs with h1 h2
  · rw [hpk_mulVec, if_pos]
    · congr 1
      ext
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val
      omega
  · rw [hpk_mulVec, if_neg h1, if_pos h2, neg_neg]
  · rw [hpk_mulVec, if_neg h1, if_neg h2]

theorem mat_eq_of_mulVec {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem hpk_sq : Hpk k r * Hpk k r = 1 := mat_eq_of_mulVec (fun v => by
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec])

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem gv_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem gv_inv_eq {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (gv_left_inv hg)

theorem gv_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [gv_inv_eq hg]
  exact gv_left_inv hg

theorem gv_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (gv_inv_mul hg))

theorem gv_one : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem gv_mul {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem gv_inv_mem {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := gv_mul_inv hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem gv_inv_inv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹⁻¹ = g := Matrix.inv_eq_left_inv (gv_mul_inv hg)

theorem hpk_mem : Hpk k r ∈ GV k r := by
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [hpk_conjT, hpk_sq, Matrix.one_mul]

theorem gN_eq_frob (g : Mat k r) :
    gN g = @Norm.norm _ (Matrix.frobeniusSeminormedAddCommGroup).toNorm g := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

theorem gN_mul_le (a b : Mat k r) : gN (a * b) ≤ gN a * gN b := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b

theorem gN_nonneg (g : Mat k r) : 0 ≤ gN g := by
  unfold gN
  exact Real.sqrt_nonneg _

theorem gN_conjT (g : Mat k r) : gN gᴴ = gN g := by
  unfold gN
  congr 1
  rw [Finset.sum_comm]
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]

theorem gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  rw [gv_inv_eq hg]
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le _ _) (gN_nonneg _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

theorem gN_one_pos : 0 < gN (1 : Mat k r) := by
  unfold gN
  apply Real.sqrt_pos.mpr
  have h0 : (0 : ℝ) < Complex.normSq ((1 : Mat k r) 0 0) := by simp
  calc (0 : ℝ) < Complex.normSq ((1 : Mat k r) 0 0) := h0
    _ ≤ ∑ j, Complex.normSq ((1 : Mat k r) 0 j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq ((1 : Mat k r) 0 j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ 0)
    _ ≤ ∑ i, ∑ j, Complex.normSq ((1 : Mat k r) i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq ((1 : Mat k r) i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ 0)

theorem gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have h1 := gN_mul_le g⁻¹ g
  rw [gv_inv_mul hg] at h1
  rcases (gN_nonneg g).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, mul_zero] at h1
    linarith [gN_one_pos (k := k) (r := r)]

def KH (k r : ℕ) : ℝ := gN (Hpk k r) ^ 2

theorem KH_pos : 0 < KH k r := by
  unfold KH
  exact pow_pos (gN_pos hpk_mem) 2

theorem gN_le_inv {g : Mat k r} (hg : g ∈ GV k r) : gN g ≤ KH k r * gN g⁻¹ := by
  unfold KH
  have h := gN_inv_le (gv_inv_mem hg)
  rwa [gv_inv_inv hg] at h

theorem rpow_neg_le {x y c b : ℝ} (hy : 0 < y) (hc : 0 < c) (hb : 0 ≤ b) (h : y ≤ c * x) :
    x ^ (-b) ≤ c ^ b * y ^ (-b) := by
  have hx : 0 < x := by
    by_contra hx
    push_neg at hx
    nlinarith
  have hA : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  have hB : 0 < y ^ b := Real.rpow_pos_of_pos hy b
  have hC : 0 < c ^ b := Real.rpow_pos_of_pos hc b
  have key : y ^ b ≤ c ^ b * x ^ b := by
    rw [← Real.mul_rpow hc.le hx.le]
    exact Real.rpow_le_rpow hy.le h hb
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  have e : c ^ b * (y ^ b)⁻¹ - (x ^ b)⁻¹ = (c ^ b * x ^ b - y ^ b) / (x ^ b * y ^ b) := by
    field_simp <;> ring
  have h2 : 0 ≤ (c ^ b * x ^ b - y ^ b) / (x ^ b * y ^ b) :=
    div_nonneg (by linarith) (mul_pos hA hB).le
  linarith

theorem uw_gv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h ∈ GV k r := hh.1

theorem n_gv {m : Mat k r} (hm : m ∈ Nset k r) : m ∈ GV k r := hm.1

theorem uw_inv_mem {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hG, hE, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := gv_inv_mul hG
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨gv_inv_mem hG, fun a => ⟨fix _ (hE a).1, fix _ (hE a).2⟩, fix _ hz⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem sig_mul (X : SigData k r) {x y : Mat k r} (hx : x ∈ GV k r) (hy : y ∈ GV k r) :
    X.σ (x * y) = (X.σ x).comp (X.σ y) := X.rep.1.2 x hx y hy

theorem sig_inner (X : SigData k r) {y : Mat k r} (hy : y ∈ GV k r) (u v : X.Hs) :
    ⟪X.σ y u, v⟫_ℂ = ⟪u, X.σ y⁻¹ v⟫_ℂ := by
  have hyi : y⁻¹ ∈ GV k r := gv_inv_mem hy
  have hcomp : X.σ y (X.σ y⁻¹ v) = v := by
    have h := X.rep.1.2 y hy y⁻¹ hyi
    rw [gv_mul_inv hy, X.rep.1.1] at h
    have h2 := DFunLike.congr_fun h v
    simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at h2
    exact h2.symm
  let L : X.Hs →ₗᵢ[ℂ] X.Hs :=
    { toLinearMap := (X.σ y).toLinearMap, norm_map' := fun w => X.rep.2.1 y hy w }
  calc ⟪X.σ y u, v⟫_ℂ = ⟪X.σ y u, X.σ y (X.σ y⁻¹ v)⟫_ℂ := by rw [hcomp]
    _ = ⟪L u, L (X.σ y⁻¹ v)⟫_ℂ := rfl
    _ = ⟪u, X.σ y⁻¹ v⟫_ℂ := L.inner_map_map _ _

theorem C_nonneg {E : Type} [NormedAddCommGroup E] {f : Mat k r → E} {C e : ℝ}
    (h : ∀ x ∈ GV k r, ‖f x‖ ≤ C * gN x ^ e) : 0 ≤ C := by
  have h1 := h 1 gv_one
  have hp : 0 < gN (1 : Mat k r) ^ e := Real.rpow_pos_of_pos gN_one_pos e
  by_contra hC
  push_neg at hC
  have h2 : C * gN (1 : Mat k r) ^ e < 0 := mul_neg_of_neg_of_pos hC hp
  linarith [norm_nonneg (f 1)]

theorem w_mem (X : SigData k r) : X.w ∈ Vfl X := ⟨X.Cw, X.dec⟩

theorem sig_mem_vfl (X : SigData k r) (ha : 0 ≤ X.a) {g : Mat k r} (hg : g ∈ GV k r) {u : X.Hs}
    (hu : u ∈ Vfl X) : X.σ g u ∈ Vfl X := by
  obtain ⟨C, hC⟩ := hu
  have hgi : g⁻¹ ∈ GV k r := gv_inv_mem hg
  have hc : 0 < gN g⁻¹ := gN_pos hgi
  have hC0 : 0 ≤ C := C_nonneg (f := mc X u X.w) hC
  refine ⟨C * gN g⁻¹ ^ X.a, fun x hx => ?_⟩
  have hxg : x * g ∈ GV k r := gv_mul hx hg
  have e : mc X (X.σ g u) X.w x = mc X u X.w (x * g) := by
    unfold mc
    rw [sig_mul X hx hg, ContinuousLinearMap.comp_apply]
  rw [e]
  have hy : 0 < gN x := gN_pos hx
  have hle : gN x ≤ gN g⁻¹ * gN (x * g) := by
    have h1 := gN_mul_le (x * g) g⁻¹
    rw [Matrix.mul_assoc, gv_mul_inv hg, Matrix.mul_one] at h1
    rw [mul_comm (gN g⁻¹)]
    exact h1
  have key := rpow_neg_le hy hc ha hle
  calc ‖mc X u X.w (x * g)‖ ≤ C * gN (x * g) ^ (-X.a) := hC _ hxg
    _ ≤ C * (gN g⁻¹ ^ X.a * gN x ^ (-X.a)) := mul_le_mul_of_nonneg_left key hC0
    _ = C * gN g⁻¹ ^ X.a * gN x ^ (-X.a) := by ring

theorem coef_bound (X : SigData k r) (ha : 0 ≤ X.a) {u : X.Hs} (hu : u ∈ Vfl X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ GV k r, ‖⟪X.σ y X.w, u⟫_ℂ‖ ≤ C * gN y ^ (-X.a) := by
  obtain ⟨C, hC⟩ := hu
  have hC0 : 0 ≤ C := C_nonneg (f := mc X u X.w) hC
  refine ⟨C * KH k r ^ X.a, mul_nonneg hC0 (Real.rpow_pos_of_pos KH_pos _).le, fun y hy => ?_⟩
  have hyi : y⁻¹ ∈ GV k r := gv_inv_mem hy
  rw [sig_inner X hy]
  have key := rpow_neg_le (gN_pos hy) KH_pos ha (gN_le_inv hy)
  calc ‖⟪X.w, X.σ y⁻¹ u⟫_ℂ‖ = ‖mc X u X.w y⁻¹‖ := rfl
    _ ≤ C * gN y⁻¹ ^ (-X.a) := hC _ hyi
    _ ≤ C * (KH k r ^ X.a * gN y ^ (-X.a)) := mul_le_mul_of_nonneg_left key hC0
    _ = C * KH k r ^ X.a * gN y ^ (-X.a) := by ring

theorem psi_norm (D : RealPlaceData k r Wp Wp) (m : Mat k r) : ‖psiD D m‖ = 1 := by
  unfold psiD psi
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem pi_norm_le (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) : ‖D.π h‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
  rw [D.π_unitary h hh v, one_mul])

theorem ae_UN (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 ∈ UWset k r D.z ∧ Matrix.of p.2 ∈ Nset k r := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.mpr D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.mpr D.haarN.conc
  exact ((Measure.quasiMeasurePreserving_fst (μ := D.μW) (ν := D.μN)).ae hW).and
    ((Measure.quasiMeasurePreserving_snd (μ := D.μW) (ν := D.μN)).ae hN)

theorem be_bound (D : RealPlaceData k r Wp Wp) (X : SigData k r) {v : X.Hs} {b Cp : ℝ} (hb0 : 0 ≤ b)
    (hCp : ∀ x ∈ GV k r, ‖mc X X.w v x‖ ≤ Cp * gN x ^ (-b))
    (hS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN)) :
    ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b := by
  have hCp0 : 0 ≤ Cp := C_nonneg (f := mc X X.w v) hCp
  refine ⟨Cp * KH k r ^ b * ∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN),
    fun y hy => ?_⟩
  have bound : ∀ᵐ p ∂(D.μW.prod D.μN), ‖beInt D X (X.σ y X.w) v p‖ ≤
      (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by
    filter_upwards [ae_UN D] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hW : Matrix.of p.1 ∈ GV k r := uw_gv hp1
    have hN : Matrix.of p.2 ∈ GV k r := n_gv hp2
    have hnw : Matrix.of p.2 * Matrix.of p.1 ∈ GV k r := gv_mul hN hW
    have hnwy : Matrix.of p.2 * Matrix.of p.1 * y ∈ GV k r := gv_mul hnw hy
    have hmc : mc X (X.σ y X.w) v (Matrix.of p.2 * Matrix.of p.1) =
        mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y) := by
      unfold mc
      rw [sig_mul X hnw hy, ContinuousLinearMap.comp_apply]
    have hpos : 0 < gN (Matrix.of p.2 * Matrix.of p.1) := gN_pos hnw
    have hle : gN (Matrix.of p.2 * Matrix.of p.1) ≤
        (KH k r * gN y) * gN (Matrix.of p.2 * Matrix.of p.1 * y) := by
      have h1 := gN_mul_le (Matrix.of p.2 * Matrix.of p.1 * y) y⁻¹
      rw [Matrix.mul_assoc _ y, gv_mul_inv hy, Matrix.mul_one] at h1
      have h2 : gN y⁻¹ ≤ KH k r * gN y := gN_inv_le hy
      calc gN (Matrix.of p.2 * Matrix.of p.1)
          ≤ gN (Matrix.of p.2 * Matrix.of p.1 * y) * gN y⁻¹ := h1
        _ ≤ gN (Matrix.of p.2 * Matrix.of p.1 * y) * (KH k r * gN y) :=
            mul_le_mul_of_nonneg_left h2 (gN_nonneg _)
        _ = (KH k r * gN y) * gN (Matrix.of p.2 * Matrix.of p.1 * y) := mul_comm _ _
    have key := rpow_neg_le hpos (mul_pos KH_pos (gN_pos hy)) hb0 hle
    have hpi : ‖D.π (Matrix.of p.1)⁻¹‖ ≤ 1 := pi_norm_le D (uw_inv_mem hp1)
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one, hmc]
    calc ‖mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y)‖ * ‖D.π (Matrix.of p.1)⁻¹‖
        ≤ ‖mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y)‖ * 1 :=
          mul_le_mul_of_nonneg_left hpi (norm_nonneg _)
      _ ≤ Cp * gN (Matrix.of p.2 * Matrix.of p.1 * y) ^ (-b) := by
          rw [mul_one]
          exact hCp _ hnwy
      _ ≤ Cp * ((KH k r * gN y) ^ b * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) :=
          mul_le_mul_of_nonneg_left key hCp0
      _ = Cp * (KH k r * gN y) ^ b * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by ring
  have hint : Integrable (fun p : Mt k r × Mt k r =>
      (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN) :=
    hS.const_mul _
  unfold beOp
  calc ‖∫ p, beInt D X (X.σ y X.w) v p ∂(D.μW.prod D.μN)‖
      ≤ ∫ p, (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)
          ∂(D.μW.prod D.μN) := norm_integral_le_of_norm_le hint bound
    _ = (Cp * (KH k r * gN y) ^ b) *
          ∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN) :=
        integral_const_mul _ _
    _ = Cp * KH k r ^ b * (∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN)) *
          gN y ^ b := by
        rw [Real.mul_rpow KH_pos.le (gN_nonneg y)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem gv_closed : IsClosed (GV k r) := by
  unfold GV UH Hpk
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem cont_of : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) := by
  exact continuous_id

theorem gv_measurable : @MeasurableSet (Mt k r) _ (GV k r) := by
  exact (show IsClosed (X := Mt k r) (GV k r) from gv_closed).measurableSet

theorem gN_cont : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := by
  unfold gN
  first
  | fun_prop
  | continuity

theorem ae_G (D : RealPlaceData k r Wp Wp) : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r := by
  exact ae_iff.mpr D.haarG.conc

theorem aesm_G {E : Type} [NormedAddCommGroup E] (D : RealPlaceData k r Wp Wp) {f : Mt k r → E}
    (hf : ContinuousOn f (GV k r : Set (Mt k r))) : AEStronglyMeasurable f D.μG := by
  have hr : D.μG.restrict (GV k r : Set (Mt k r)) = D.μG := Measure.restrict_eq_self_of_ae_mem (ae_G D)
  rw [← hr]
  exact hf.aestronglyMeasurable gv_measurable

theorem test_cont {φ : Mat k r → ℂ} (hφ : IsTestG φ) : ContinuousOn φ (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hφf⟩ := hφ.1 g₀ hg₀
  have hc : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hφf g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hg₀U)] with g hg using hφf g hg.2 hg.1

theorem test_bound {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    ∃ K : Set (Mat k r), IsCompact K ∧ ∃ M : ℝ, 0 ≤ M ∧ ∃ R : ℝ, 0 ≤ R ∧ (∀ x ∈ K, gN x ≤ R) ∧
      ∀ x ∈ GV k r, ‖φ x‖ ≤ M * K.indicator 1 x := by
  obtain ⟨K, hK, hK0⟩ := hφ.2
  have hKc : IsCompact (K ∩ GV k r) := hK.inter_right gv_closed
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((test_cont hφ).mono Set.inter_subset_right)
  have hgN : ContinuousOn (fun x : Mat k r => gN x) (K ∩ GV k r) :=
    (show Continuous (fun x : Mat k r => gN x) from gN_cont).continuousOn
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn hgN
  refine ⟨K ∩ GV k r, hKc, max M 0, le_max_right _ _, max R 0, le_max_right _ _, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := hR x hx
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  · by_cases hxK : x ∈ K
    · have hx' : x ∈ K ∩ GV k r := ⟨hxK, hx⟩
      rw [Set.indicator_of_mem hx', Pi.one_apply, mul_one]
      exact (hM x hx').trans (le_max_left _ _)
    · rw [hK0 x hx hxK]
      simp [Set.indicator_apply, hxK]

theorem int_ind (D : RealPlaceData k r Wp Wp) {K : Set (Mat k r)} (hK : IsCompact K) :
    Integrable (fun x : Mt k r => K.indicator (1 : Mat k r → ℝ) (Matrix.of x)) D.μG := by
  have hm : @MeasurableSet (Mt k r) _ K := (show IsClosed (X := Mt k r) K from hK.isClosed).measurableSet
  have hfin : D.μG K < ⊤ := D.haarG.finite_compact K hK
  have he : (fun x : Mt k r => K.indicator (1 : Mat k r → ℝ) (Matrix.of x)) = @Set.indicator (Mt k r) ℝ _ K 1 := rfl
  rw [he]
  refine (integrable_indicator_iff hm).2 ?_
  first
  | exact integrableOn_const.2 (Or.inr hfin)
  | exact integrableOn_const hfin.ne
  | exact integrableOn_const (C := (1 : ℝ)) hfin.ne

theorem gN_integrable (D : RealPlaceData k r Wp Wp) (hGN : GNIntSharp) {A : ℝ} (hA : AB k r ≤ A) :
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-A)) D.μG := by
  unfold GNIntSharp AB at *
  refine ⟨(gN_cont.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => ?_)).2 (hGN k r D.μG A D.haarG hA)
  show 0 ≤ gN (Matrix.of y) ^ (-A)
  exact Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _

theorem orbit_bound (X : SigData k r) (ha0 : 0 ≤ X.a) {x y : Mat k r} (hx : x ∈ GV k r) (hy : y ∈ GV k r) :
    ‖⟪X.σ y X.w, X.σ x X.w⟫_ℂ‖ ≤ X.Cw * ((KH k r ^ 2 * gN x) ^ X.a * gN y ^ (-X.a)) := by
  have hyx : y⁻¹ * x ∈ GV k r := gv_mul (gv_inv_mem hy) hx
  rw [sig_inner X hy, ← ContinuousLinearMap.comp_apply, ← sig_mul X (gv_inv_mem hy) hx]
  have h1 : gN y ≤ (KH k r ^ 2 * gN x) * gN (y⁻¹ * x) := by
    calc gN y ≤ KH k r * gN y⁻¹ := gN_le_inv hy
      _ = KH k r * gN (y⁻¹ * x * x⁻¹) := by rw [Matrix.mul_assoc, gv_mul_inv hx, Matrix.mul_one]
      _ ≤ KH k r * (gN (y⁻¹ * x) * gN x⁻¹) := mul_le_mul_of_nonneg_left (gN_mul_le _ _) KH_pos.le
      _ ≤ KH k r * (gN (y⁻¹ * x) * (KH k r * gN x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gN_inv_le hx) (gN_nonneg _)) KH_pos.le
      _ = _ := by unfold KH; ring
  calc ‖⟪X.w, X.σ (y⁻¹ * x) X.w⟫_ℂ‖ ≤ X.Cw * gN (y⁻¹ * x) ^ (-X.a) := X.dec _ hyx
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_neg_le (gN_pos hy) (mul_pos (pow_pos KH_pos 2) (gN_pos hx)) ha0 h1)
        (C_nonneg X.dec)

theorem sig_aesm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (v : X.Hs) :
    AEStronglyMeasurable (fun y : Mt k r => X.σ (Matrix.of y) v) D.μG :=
  aesm_G D (X.rep.2.2 v)

theorem sigInt_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    Integrable (fun g : Mt k r => φ (Matrix.of g) • X.σ (Matrix.of g) X.w) D.μG := by
  obtain ⟨K, hK, M, hM0, R, hR0, hKR, hb⟩ := test_bound hφ
  refine Integrable.mono' ((int_ind D hK).const_mul M) ?_ ?_
  · exact aesm_G D ((test_cont hφ).smul (X.rep.2.2 X.w))
  · filter_upwards [ae_G D] with g hg
    rw [norm_smul, X.rep.2.1 _ hg, X.w_norm, mul_one]
    exact hb _ hg

theorem dd_mem (D : RealPlaceData k r Wp Wp) (X : SigData k r) (ha0 : 0 ≤ X.a) {φ : Mat k r → ℂ}
    (hφ : IsTestG φ) : sigInt D X φ X.w ∈ Vfl X := by
  obtain ⟨K, hK, M, hM0, R, hR0, hRK, hM⟩ := test_bound hφ
  have hint := sigInt_integrable D X hφ
  have hCw := C_nonneg X.dec
  refine ⟨M * X.Cw * (KH k r * R) ^ X.a * ∫ g : Mt k r, K.indicator (1 : Mat k r → ℝ) (Matrix.of g) ∂D.μG,
    fun x hx => ?_⟩
  have e1 : mc X (sigInt D X φ X.w) X.w x =
      ∫ g : Mt k r, ⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ ∂D.μG := by
    unfold mc sigInt
    rw [← (X.σ x).integral_comp_comm hint, integral_inner ((X.σ x).integrable_comp hint)]
  rw [e1]
  have hb : ∀ᵐ g ∂D.μG, ‖⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ‖ ≤
      (M * X.Cw * (KH k r * R) ^ X.a * gN x ^ (-X.a)) * K.indicator (1 : Mat k r → ℝ) (Matrix.of g) := by
    filter_upwards [ae_G D] with g hg
    rw [map_smul, inner_smul_right, norm_mul, ← ContinuousLinearMap.comp_apply, ← sig_mul X hx hg]
    by_cases hgK : Matrix.of g ∈ K
    · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of g) = 1 := by simp [Set.indicator, hgK]
      have hφg : ‖φ (Matrix.of g)‖ ≤ M := by simpa [hi] using hM _ hg
      have h1 : gN x ≤ (KH k r * R) * gN (x * Matrix.of g) := by
        calc gN x = gN (x * Matrix.of g * (Matrix.of g)⁻¹) := by
              rw [Matrix.mul_assoc, gv_mul_inv hg, Matrix.mul_one]
          _ ≤ gN (x * Matrix.of g) * gN (Matrix.of g)⁻¹ := gN_mul_le _ _
          _ ≤ gN (x * Matrix.of g) * (KH k r * R) := by
              refine mul_le_mul_of_nonneg_left ((gN_inv_le hg).trans ?_) (gN_nonneg _)
              exact mul_le_mul_of_nonneg_left (hRK _ hgK) KH_pos.le
          _ = _ := mul_comm _ _
      have h2 : ‖⟪X.w, X.σ (x * Matrix.of g) X.w⟫_ℂ‖ ≤ X.Cw * ((KH k r * R) ^ X.a * gN x ^ (-X.a)) :=
        (X.dec _ (gv_mul hx hg)).trans (mul_le_mul_of_nonneg_left
          (rpow_neg_le (gN_pos hx) (mul_pos KH_pos ((gN_pos hg).trans_le (hRK _ hgK))) ha0 h1) hCw)
      rw [hi, mul_one]
      calc ‖φ (Matrix.of g)‖ * ‖⟪X.w, X.σ (x * Matrix.of g) X.w⟫_ℂ‖
          ≤ M * (X.Cw * ((KH k r * R) ^ X.a * gN x ^ (-X.a))) :=
            mul_le_mul hφg h2 (norm_nonneg _) hM0
        _ = _ := by ring
    · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of g) = 0 := by simp [Set.indicator, hgK]
      have hφg : φ (Matrix.of g) = 0 := by
        have := hM _ hg; rw [hi, mul_zero] at this; exact norm_le_zero_iff.1 this
      rw [hi, hφg]; simp
  calc ‖∫ g : Mt k r, ⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ ∂D.μG‖
      ≤ ∫ g : Mt k r, (M * X.Cw * (KH k r * R) ^ X.a * gN x ^ (-X.a)) *
          K.indicator (1 : Mat k r → ℝ) (Matrix.of g) ∂D.μG :=
        norm_integral_le_of_norm_le ((int_ind D hK).const_mul _) hb
    _ = _ := by rw [integral_const_mul]; ring

theorem test_of_contDiff {g : Mt k r → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    IsTestG (fun x : Mat k r => ((g x : ℝ) : ℂ)) := by
  unfold IsTestG CkOn
  refine ⟨fun g₀ _ => ⟨Set.univ, fun x => ((g x : ℝ) : ℂ), isOpen_univ, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩,
    tsupport g, hgc, fun x _ hx => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hg).contDiffOn
  · have h0 : g x = 0 := by
      first
      | exact image_eq_zero_of_notMem_tsupport hx
      | exact image_eq_zero_of_nmem_tsupport hx
    simp [h0]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem mulVec_cont (v : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => g *ᵥ v) := by
  fun_prop

theorem uw_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  unfold UWset
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  have hc : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mat k r | g *ᵥ v = v} :=
    fun v => isClosed_eq (mulVec_cont v) continuous_const
  exact gv_closed.inter ((isClosed_iInter fun a => (hc _).inter (hc _)).inter (hc z))

theorem n_closed : IsClosed (Nset k r) := by
  unfold Nset
  have he : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ), IsClosed {g : Mat k r | g i j = c} :=
    fun i j c => isClosed_eq (continuous_id.matrix_elem i j) continuous_const
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  exact gv_closed.inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => he _ _ _).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => he _ _ _))

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (fun m : Mat k r => psi k r z cStd m) := by
  unfold psi ell
  have hs : Continuous fun m : Mat k r => ∑ a : Fin r, (if h : (a : ℕ) + 1 < r then m (eI k r a) (eI k r ⟨(a : ℕ) + 1, h⟩)
      else (m *ᵥ z) (eI k r a)) := by
    refine continuous_finset_sum _ fun a _ => ?_
    by_cases h : (a : ℕ) + 1 < r
    · simp only [dif_pos h]
      exact continuous_id.matrix_elem _ _
    · simp only [dif_neg h]
      show Continuous ((fun v : Fin (2 * r + k + 1) → ℂ => v (eI k r a)) ∘ fun m : Mat k r => m *ᵥ z)
      exact (continuous_apply (eI k r a)).comp (mulVec_cont z)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul hs))))

theorem be_aesm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (v : X.Hs) :
    AEStronglyMeasurable (fun y : Mt k r => beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  have sW := (⟨fun K hK => D.haarW.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μW)
  have sN := (⟨fun K hK => D.haarN.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μN)
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  set S3 : Set (Mt k r × (Mt k r × Mt k r)) := {z | Matrix.of z.1 ∈ GV k r ∧
    Matrix.of z.2.1 ∈ UWset k r D.z ∧ Matrix.of z.2.2 ∈ Nset k r} with hS3
  have hS3c : IsClosed S3 :=
    IsClosed.inter (gv_closed.preimage (cont_of.comp continuous_fst))
      (IsClosed.inter ((uw_closed D.z).preimage (cont_of.comp (continuous_fst.comp continuous_snd)))
        (n_closed.preimage (cont_of.comp (continuous_snd.comp continuous_snd))))
  have hae : ∀ᵐ z ∂(D.μG.prod (D.μW.prod D.μN)), z ∈ S3 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_G D),
      Measure.quasiMeasurePreserving_snd.ae (ae_UN D)] with z h1 h2
    exact ⟨h1, h2.1, h2.2⟩
  set G : Mt k r × (Mt k r × Mt k r) → (Wp →L[ℂ] Wp) := fun z =>
    (⟪v, X.σ (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1) X.w⟫_ℂ *
      star (psiD D (Matrix.of z.2.2))) • D.π (Hpk k r * (Matrix.of z.2.1)ᴴ * Hpk k r) with hG
  have hGc : ContinuousOn G S3 := by
    have hm : Continuous (fun z : Mt k r × (Mt k r × Mt k r) =>
        (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1 : Mat k r)) :=
      ((cont_of.comp (continuous_snd.comp continuous_snd)).matrix_mul
        (cont_of.comp (continuous_fst.comp continuous_snd))).matrix_mul (cont_of.comp continuous_fst)
    have c1 : ContinuousOn (fun z : Mt k r × (Mt k r × Mt k r) =>
        X.σ (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1) X.w) S3 :=
      (X.rep.2.2 X.w).comp hm.continuousOn fun z hz => gv_mul (gv_mul (n_gv hz.2.2) (uw_gv hz.2.1)) hz.1
    have c2 : Continuous (fun z : Mt k r × (Mt k r × Mt k r) => star (psiD D (Matrix.of z.2.2))) :=
      continuous_star.comp ((psi_cont D.z).comp (cont_of.comp (continuous_snd.comp continuous_snd)))
    have hi : Continuous (fun z : Mt k r × (Mt k r × Mt k r) => Hpk k r * (Matrix.of z.2.1 : Mat k r)ᴴ * Hpk k r) :=
      (continuous_const.matrix_mul (cont_of.comp (continuous_fst.comp continuous_snd)).matrix_conjTranspose).matrix_mul
        continuous_const
    have c3 : ContinuousOn (fun z : Mt k r × (Mt k r × Mt k r) => D.π (Hpk k r * (Matrix.of z.2.1)ᴴ * Hpk k r)) S3 :=
      D.π_cont.comp hi.continuousOn fun z hz => by
        have := uw_inv_mem hz.2.1
        rwa [gv_inv_eq (uw_gv hz.2.1)] at this
    exact ((continuousOn_const.inner c1).mul c2.continuousOn).smul c3
  have hGm : AEStronglyMeasurable G (D.μG.prod (D.μW.prod D.μN)) := by
    have h := ContinuousOn.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) hGc hS3c.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h
  have hFm : AEStronglyMeasurable (fun z : Mt k r × (Mt k r × Mt k r) =>
      beInt D X (X.σ (Matrix.of z.1) X.w) v z.2) (D.μG.prod (D.μW.prod D.μN)) := by
    refine hGm.congr ?_
    filter_upwards [hae] with z hz
    have hs : Matrix.of z.2.2 * Matrix.of z.2.1 ∈ GV k r := gv_mul (n_gv hz.2.2) (uw_gv hz.2.1)
    simp only [hG, beInt, mc]
    rw [sig_mul X hs hz.1, ContinuousLinearMap.comp_apply, gv_inv_eq (uw_gv hz.2.1)]
  exact hFm.integral_prod_right'

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def MinorsOn (D : RealPlaceData k r Wp Wp) (X : SigData k r) : Prop :=
  ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
    ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ =
      ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

lemma beInt_add_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u v u' : X.Hs) (p : Mt k r × Mt k r) :
    beInt D X (u + v) u' p = beInt D X u u' p + beInt D X v u' p := by
  simp only [beInt, mc, map_add, inner_add_right, add_mul, add_smul]

lemma beInt_smul_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (c : ℂ) (u u' : X.Hs)
    (p : Mt k r × Mt k r) : beInt D X (c • u) u' p = c • beInt D X u u' p := by
  simp only [beInt, mc, map_smul, inner_smul_right, smul_smul, mul_assoc]

theorem beInt_integrable_of (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) :
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN) := by
  intro u hu u' hu'
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd X.a X.a u hu u' hu'
  refine h1' k r Wp D X hD hX (X.a - AG k r - 1) ?_ u u' ⟨C, ?_⟩
  · have hn : (1 : ℝ) ≤ nR k r := by
      unfold nR
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    unfold AS AG
    unfold aM at ha
    nlinarith [mul_nonneg (sub_nonneg.2 hn) (by positivity : (0 : ℝ) ≤ 3 * nR k r ^ 2 + 2 * nR k r + 2)]
  · simpa [min_self] using hC

theorem multOne_of_minors (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hP : ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re)
    (hInt : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN))
    (hEq : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u'))
    (hM : MinorsOn D X) : ∃ l : X.Hs → Wp, IsMultOneMap D X l := by
  have hre : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = ((⟪ξ, beOp D X u u ξ⟫_ℂ).re : ℂ) := by
    intro u hu ξ
    have h1 := hH u hu u hu ξ ξ
    have h2 : starRingEnd ℂ ⟪ξ, beOp D X u u ξ⟫_ℂ = ⟪ξ, beOp D X u u ξ⟫_ℂ := by
      rw [inner_conj_symm]; exact h1.symm
    exact (Complex.conj_eq_iff_re.mp h2).symm
  by_cases h0 : ∃ v₀ ∈ Vfl X, ∃ ξ₀ : Wp, 0 < (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re
  · obtain ⟨v₀, hv₀, ξ₀, hpos⟩ := h0
    set κ₀ : ℝ := (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re with hκ₀
    set c : ℂ := (((Real.sqrt κ₀)⁻¹ : ℝ) : ℂ) with hc
    refine ⟨fun u => c • beOp D X u v₀ ξ₀, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu v hv
      have : beOp D X (u + v) v₀ = beOp D X u v₀ + beOp D X v v₀ := by
        unfold beOp
        simp_rw [beInt_add_left]
        exact integral_add (hInt u hu v₀ hv₀) (hInt v hv v₀ hv₀)
      simp only [this, _root_.add_apply, smul_add]
    · intro a u hu
      have : beOp D X (a • u) v₀ = a • beOp D X u v₀ := by
        unfold beOp
        simp_rw [beInt_smul_left]
        exact integral_smul a _
      simp only [this, _root_.smul_apply]
      rw [smul_comm]
    · intro h hh m hm u hu
      simp only [hEq u hu v₀ hv₀ h hh m hm, _root_.smul_apply,
        ContinuousLinearMap.comp_apply, map_smul]
      rw [smul_comm]
    · intro u hu u' hu'
      ext η'
      apply ext_inner_left ℂ
      intro η
      simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
        inner_smul_left]
      rw [← hH v₀ hv₀ u' hu' η' ξ₀]
      have hmin := hM u hu u' hu' v₀ hv₀ v₀ hv₀ η η' ξ₀ ξ₀
      rw [hre v₀ hv₀ ξ₀] at hmin
      have hcc : starRingEnd ℂ c * c = ((κ₀⁻¹ : ℝ) : ℂ) := by
        rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1
        rw [← mul_inv, Real.mul_self_sqrt hpos.le]
      have hk : ((κ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      calc ⟪η, beOp D X u u' η'⟫_ℂ
          = (starRingEnd ℂ c * c) * (⟪η, beOp D X u u' η'⟫_ℂ * (κ₀ : ℂ)) := by
            rw [hcc, Complex.ofReal_inv]; field_simp
        _ = _ := by rw [hmin]; ring
  · push Not at h0
    have hz : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = 0 := by
      intro u hu ξ
      rw [hre u hu ξ]
      have := le_antisymm (h0 u hu ξ) (hP u hu ξ)
      simp [this]
    refine ⟨fun _ => 0, ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩, ?_⟩
    intro u hu u' hu'
    ext η'
    apply ext_inner_left ℂ
    intro η
    have hm := hM u hu u' hu' u' hu' u hu η η' η' η
    rw [hz u hu η, zero_mul] at hm
    have hc : ⟪η', beOp D X u' u η⟫_ℂ = starRingEnd ℂ ⟪η, beOp D X u u' η'⟫_ℂ := by
      rw [hH u' hu' u hu η η', inner_conj_symm]
    rw [hc, Complex.mul_conj] at hm
    have h3 : Complex.normSq ⟪η, beOp D X u u' η'⟫_ℂ = 0 := by exact_mod_cast hm
    rw [Complex.normSq_eq_zero.mp h3]
    simp [rk1]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def Mn (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) : ℂ :=
  ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
    ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

theorem kbound (B : Wp →L[ℂ] Wp) (e f : Wp) : ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖f‖ * ‖B‖ := by
  calc ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖B f‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖B‖ * ‖f‖) := mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg _)
    _ = _ := by ring

theorem joint_int (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {b Cl : ℝ} (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    Integrable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2) *
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ * Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := by
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  obtain ⟨K, hK, M, hM0, R, hR0, hRK, hM⟩ := test_bound hφ
  have a1 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2)) (D.μG.prod D.μG) :=
    (aesm_G D (test_cont hφ)).comp_snd
  have a2 : AEStronglyMeasurable (fun z : Mt k r × Mt k r =>
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ) (D.μG.prod D.μG) :=
    ((sig_aesm D X X.w).comp_fst).inner ((sig_aesm D X X.w).comp_snd)
  have a3 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := hlm.comp_fst
  have hint : Integrable (fun z : Mt k r × Mt k r =>
      (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl * gN (Matrix.of z.1) ^ (-(X.a - b))) *
        K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2)) (D.μG.prod D.μG) :=
    ((gN_integrable D hGN hab).const_mul (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl)).mul_prod (int_ind D hK)
  refine hint.mono' ((a1.mul a2).mul a3) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_G D),
    Measure.quasiMeasurePreserving_snd.ae (ae_G D)] with z hz1 hz2
  have hKp : 0 ≤ (KH k r ^ 2 * R) ^ X.a := Real.rpow_nonneg (mul_nonneg (pow_pos KH_pos 2).le hR0) _
  have hCw := C_nonneg X.dec
  by_cases hxK : Matrix.of z.2 ∈ K
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 1 := by simp [Set.indicator, hxK]
    have hφx : ‖φ (Matrix.of z.2)‖ ≤ M := by simpa [hi] using hM _ hz2
    have hO' : ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ ≤
        X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a)) :=
      (orbit_bound X ha0 hz2 hz1).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (mul_nonneg (pow_pos KH_pos 2).le (gN_nonneg _))
          (mul_le_mul_of_nonneg_left (hRK _ hxK) (pow_pos KH_pos 2).le) ha0)
        (Real.rpow_nonneg (gN_nonneg _) _)) hCw)
    have hl := hCl _ hz1
    have e : gN (Matrix.of z.1) ^ (-(X.a - b)) =
        gN (Matrix.of z.1) ^ (-X.a) * gN (Matrix.of z.1) ^ b := by
      rw [← Real.rpow_add (gN_pos hz1)]; ring_nf
    rw [norm_mul, norm_mul, hi, mul_one, e]
    calc ‖φ (Matrix.of z.2)‖ * ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ *
          ‖Λ (X.σ (Matrix.of z.1) X.w)‖
        ≤ M * (X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a))) *
          (Cl * gN (Matrix.of z.1) ^ b) :=
          mul_le_mul (mul_le_mul hφx hO' (norm_nonneg _) hM0) hl (norm_nonneg _)
            (mul_nonneg hM0 (mul_nonneg hCw (mul_nonneg hKp (Real.rpow_nonneg (gN_nonneg _) _))))
      _ = _ := by ring
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 0 := by simp [Set.indicator, hxK]
    have hφx : φ (Matrix.of z.2) = 0 := by
      have := hM _ hz2; rw [hi, mul_zero] at this; exact norm_le_zero_iff.1 this
    rw [hφx, hi]
    simp

theorem step_ii (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b Cl : ℝ} (hd : 0 < d) (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    ∫ x : Mt k r, φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) ∂D.μG = Λ (sigInt D X φ X.w) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hint := sigInt_integrable D X hφ
  have hc : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, sigInt D X φ X.w⟫_ℂ =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG := by
    intro y
    unfold sigInt
    rw [← integral_inner hint]
    simp only [inner_smul_right]
  have hFi := joint_int D X hGN ha0 hCl0 hab Λ hlm hCl hφ
  have e1 : Λ (sigInt D X φ X.w) = (d : ℂ) * ∫ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) ∂D.μG := by
    rw [hR _ (dd_mem D X ha0 hφ)]
    simp only [hc]
  have e2 : ∀ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG := fun y => (integral_mul_const _ _).symm
  have e3 := integral_integral_swap (μ := D.μG) (ν := D.μG) (f := fun y x : Mt k r => φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ * Λ (X.σ (Matrix.of y) X.w)) hFi
  have e4 : ∀ᵐ x ∂D.μG, ∫ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG = φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) / d := by
    filter_upwards [ae_G D] with x hx
    have hx' := hR _ (sig_mem_vfl X ha0 hx (w_mem X))
    have e5 : ∀ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) = φ (Matrix.of x) * (⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w)) := fun y => mul_assoc _ _ _
    simp only [e5]
    rw [integral_const_mul, hx']
    field_simp
  rw [e1]
  simp only [e2]
  rw [e3, integral_congr_ae e4, integral_div]
  field_simp

theorem vanish_core (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hlb : ∃ C : ℝ, ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ C * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    (h0 : ∀ φ : Mat k r → ℂ, IsTestG φ → Λ (sigInt D X φ X.w) = 0) :
    ∀ u ∈ Vfl X, Λ u = 0 := by
  obtain ⟨Cl, hCl⟩ := hlb
  have hCl0 : 0 ≤ Cl := C_nonneg hCl
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hli : LocallyIntegrable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG := by
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn gN_cont.continuousOn
    have hfin : IsFiniteMeasure (D.μG.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact D.haarG.finite_compact K hK⟩
    refine Integrable.mono' (integrable_const (Cl * (max R 0) ^ b)) hlm.restrict ?_
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae (ae_G D)] with y hyK hyG
    refine (hCl _ hyG).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (gN_nonneg _) ?_ hb0) hCl0)
    exact ((Real.le_norm_self _).trans (hR y hyK)).trans (le_max_left _ _)
  have hae : ∀ᵐ y ∂D.μG, Λ (X.σ (Matrix.of y) X.w) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli fun g hg hgc => ?_
    have h1 := step_ii D X hGN ha0 hd hCl0 hab Λ hlm hCl hR (test_of_contDiff hg hgc)
    rw [h0 _ (test_of_contDiff hg hgc)] at h1
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => Complex.real_smul)
  intro u hu
  rw [hR u hu]
  have : ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG = 0 :=
    integral_eq_zero_of_ae (by filter_upwards [hae] with y hy; simp [hy])
  rw [this, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_scalar (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) {u v : X.Hs} (e f : Wp)
    (hI : Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG)
    (hR : beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ) D.μG ∧
    ⟪e, beOp D X u v f⟫_ℂ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ ∂D.μG := by
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)
  have hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ := fun A => by
    simp [L, innerSL_apply_apply]
  have hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ := fun c A => by
    rw [map_smul, hL, smul_eq_mul]
  refine ⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩
  rw [hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)

theorem opint (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {b : ℝ}
    (hab : AB k r ≤ X.a - b) {u v : X.Hs} (hu : u ∈ Vfl X)
    (hbv : ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨Cc, hCc0, hCc⟩ := coef_bound X ha0 hu
  obtain ⟨Cb, hCb⟩ := hbv
  have hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG :=
    (show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from
      (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)
  refine ((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_
  filter_upwards [ae_G D] with y hy
  rw [norm_smul]
  have e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b := by
    rw [← Real.rpow_add (gN_pos hy)]; ring_nf
  rw [e]
  calc ‖⟪X.σ (Matrix.of y) X.w, u⟫_ℂ‖ * ‖beOp D X (X.σ (Matrix.of y) X.w) v‖
      ≤ (Cc * gN (Matrix.of y) ^ (-X.a)) * (Cb * gN (Matrix.of y) ^ b) :=
        mul_le_mul (hCc _ hy) (hCb _ hy) (norm_nonneg _)
          (mul_nonneg hCc0 (Real.rpow_nonneg (gN_nonneg _) _))
    _ = _ := by ring

theorem ext1 (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {d b : ℝ}
    (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    {u₂ u₄ : X.Hs} (hu₂ : u₂ ∈ Vfl X) (hu₄ : u₄ ∈ Vfl X) (u₃ : X.Hs) (e₁ e₂ e₃ e₄ : Wp)
    (h : ∀ φ : Mat k r → ℂ, IsTestG φ → Mn D X (sigInt D X φ X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) :
    ∀ u ∈ Vfl X, Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  refine vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h
  · let L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)
    let L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)
    have m2 := L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)
    have m4 := L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)
    exact (m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)
  · obtain ⟨C₂, h₂⟩ := hbe u₂ hu₂
    obtain ⟨C₄, h₄⟩ := hbe u₄ hu₄
    refine ⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
      ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩
    simp only [Mn]
    calc ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
          ⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖
        ≤ ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          ‖⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₄ y hy) (by positivity))) (norm_nonneg _))
      _ = _ := by ring
  · intro u hu
    obtain ⟨i2, r2⟩ := repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)
    obtain ⟨i4, r4⟩ := repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)
    have e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ =
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₄ e₄⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ := fun y => by simp only [Mn]; ring
    show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG
    simp only [e5]
    rw [integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]
    simp only [Mn]
    rw [r2, r4]
    ring

theorem mn_swap (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₃ u₂ u₁ u₄ e₃ e₂ e₁ e₄ = -Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ := by
  unfold Mn; ring

theorem mn_herm (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    {u₁ u₂ u₃ u₄ : X.Hs} (h₁ : u₁ ∈ Vfl X) (h₂ : u₂ ∈ Vfl X) (h₃ : u₃ ∈ Vfl X) (h₄ : u₄ ∈ Vfl X)
    (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₂ u₁ u₄ u₃ e₂ e₁ e₄ e₃ = starRingEnd ℂ (Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄) := by
  have kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp,
      ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ := by
    intro u hu v hv e f
    rw [hH v hv u hu e f, inner_conj_symm]
  unfold Mn
  rw [kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]
  simp only [map_sub, map_mul]
  ring

theorem minorsOn_of_DD (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a)
    {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hDD : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) : MinorsOn D X := by
  have hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X := fun φ hφ => ⟨φ, hφ, rfl⟩
  have S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  have S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  have S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃,
      S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]
  have S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
  have : Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  exact sub_eq_zero.1 this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end

section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem isHaarOn_smul {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) {c : ℝ≥0} (hc : 0 < c) :
    IsHaarOn U ((c : ℝ≥0∞) • μ) where
  conc := by simp [h.conc]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h0
    have h1 : (c : ℝ≥0∞) * μ Set.univ = 0 := by
      rw [← smul_eq_mul, ← Measure.smul_apply, h0]; rfl
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hc.ne')
    · exact h.ne_zero (Measure.measure_univ_eq_zero.1 h2)

def rescale (D : RealPlaceData k r Wp Wp) {c : ℝ≥0} (hc : 0 < c) : RealPlaceData k r Wp Wp :=
  { D with μG := (c : ℝ≥0∞) • D.μG, haarG := isHaarOn_smul D.haarG hc }

theorem ccInt_of (D : RealPlaceData k r Wp Wp) (hGN : GNIntSharp) {A : ℝ} (hA : AB k r ≤ A) {c : ℝ≥0} (hc : 0 < c) :
    CCIntegrable (rescale D hc) A := by
  intro F c' _ hF
  show (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂((c : ℝ≥0∞) • D.μG)) < ∞
  rw [lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hfin := hGN k r D.μG A D.haarG hA
  have hb : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤
      ENNReal.ofReal (max c' 0) * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_G D] with g hg
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos (gN_pos hg) A
    have h1 : ‖F (Matrix.of g)‖ ≤ max c' 0 * gN (Matrix.of g) ^ (-A) := by
      rw [Real.rpow_neg (gN_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hF _ hg).trans (le_max_left _ _)
    rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem jcont_of (hIn : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) : JCont D A := by
  obtain ⟨hB2, -, -, -, -, -, -, hJC, -, -, -, -, -, -, hINB, -⟩ := hIn
  obtain ⟨c, ⟨hc, hIF⟩, -⟩ := hINB k r Wp Wp D
  have hGN : GNIntSharp := hB2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact hJC k r Wp Wp (rescale D hc) A hIF (ccInt_of D hGN hA hc)

theorem lemB_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      beta D F F' = (c : ℂ) * betaInf D F F' := by
  obtain ⟨-, -, -, -, -, -, hLBX, -⟩ := hIn
  obtain ⟨c, hc, -, -, hB, -⟩ := (hLBX hXi).2 k r Wp Wp D A hA
  exact ⟨c, by exact_mod_cast hc, hB⟩

theorem hs_ext {A B : Wp →L[ℂ] Wp} (h : ∀ X₀ : Wp →L[ℂ] Wp, hsInner A X₀ = hsInner B X₀) : A = B := by
  have hlin : hsVec (A - B) = hsVec A - hsVec B := by
    ext i; simp [hsVec]
  have h1 : inner ℂ (hsVec (A - B)) (hsVec (A - B)) = 0 := by
    have := h (A - B)
    unfold hsInner at this
    rw [hlin] at this ⊢
    rw [inner_sub_right, this, sub_self]
  rw [inner_self_eq_zero] at h1
  rw [← sub_eq_zero]
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wp).toBasis.ext fun i => ?_
  have := congrArg (fun v => v i) h1
  simpa [hsVec] using this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem nR_ge (hk : 1 ≤ k) : (2 : ℝ) ≤ nR k r := by
  unfold nR
  have : 2 ≤ 2 * r + k + 1 := by omega
  exact_mod_cast this

theorem half_ratio_le_segment_base_of_std (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AB k r ≤ a - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have e : nR k r = 2 * (r : ℝ) + k + 1 := by unfold nR; push_cast; ring
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 ≤ nR k r ^ 2 := by rw [e]; nlinarith
  have h2 : 2 * nR k r ^ 2 + 1 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AB AG; unfold aM at ha
  linarith

theorem decay_exponent_ge_double_shift (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AS k r + 1 ≤ a - AG k r - 1 - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have h2 : nR k r ^ 3 + 2 * nR k r ^ 2 + 3 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AS AG; unfold aM at ha
  linarith

theorem beInt_int_mixed (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) {u v : X.Hs}
    (hu : u ∈ VflA X (X.a - AG k r - 1)) (hv : v ∈ Vfl X) : Integrable (beInt D X u v) (D.μW.prod D.μN) := by
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd (X.a - AG k r - 1) X.a u hu v hv
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hmin : min (X.a - AG k r - 1) X.a = X.a - AG k r - 1 := min_eq_left (by linarith)
  rw [hmin] at hC
  exact h1' k r Wp D X hD hX _ (decay_exponent_ge_double_shift D.k_pos ha) u v ⟨C, hC⟩

theorem psiD_one (D : RealPlaceData k r Wp Wp) : psiD D 1 = 1 := by
  have h : ∀ a : Fin r, (if h : a.val + 1 < r then (1 : Mat k r) (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else ((1 : Mat k r) *ᵥ D.z) (eI k r a)) = 0 := by
    intro a
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact D.z_mem _ (Or.inl a.isLt)
  unfold psiD psi ell
  rw [Finset.sum_eq_zero (fun a _ => h a)]
  simp

theorem pi_adj (D : RealPlaceData k r Wp Wp) {g : Mat k r} (hg : g ∈ UWset k r D.z) :
    ContinuousLinearMap.adjoint (D.π g) = D.π g⁻¹ := by
  have hgi := uw_inv_mem hg
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (D.π g : Wp →ₗ[ℂ] Wp), norm_map' := D.π_unitary g hg }
  have h1 : D.π g (D.π g⁻¹ x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← D.π_rep.2 g hg g⁻¹ hgi, gv_mul_inv (uw_gv hg), D.π_rep.1]
    rfl
  calc ⟪D.π g⁻¹ x, y⟫_ℂ = ⟪L (D.π g⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪x, D.π g y⟫_ℂ := by
        show ⟪D.π g (D.π g⁻¹ x), D.π g y⟫_ℂ = _
        rw [h1]

theorem ae_UN' (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW'.prod D.μN), Matrix.of p.1 ∈ UWset k r D.z' ∧ Matrix.of p.2 ∈ Nset k r := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have h1 : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h2 : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem ae_SS (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_UN D),
    Measure.quasiMeasurePreserving_snd.ae (ae_UN' D)] with p h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem incc_dd (hSm : StSmooth) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) {a b : X.Hs} (ha' : a ∈ DDinf D X) (hb : b ∈ DDinf D X) :
    InCC (X.a - AG k r - 1) 5 (mc X a b) := by
  obtain ⟨φ, hφ, rfl⟩ := ha'
  obtain ⟨φ', hφ', rfl⟩ := hb
  exact hSm k r Wp D X hD hX ha φ φ' hφ hφ' 5

theorem beta_val (h1p : StCut1p) (h2 : StCut2) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) {d : ℝ} (hd : IsFdegG D X d)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : ∀ g ∈ GV k r, f g = mc X x y g)
    (hfc : InCC A 5 f) (hc2 : InCC A 5 (mc X a₂ b₂))
    (hxa : Integrable (beInt D X x a₂) (D.μW.prod D.μN)) (hyb : Integrable (beInt D X y b₂) (D.μW.prod D.μN)) :
    beta D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) =
      (c : ℂ) * (hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)) := by
  obtain ⟨hI, hval⟩ := h2 k r Wp D X hD d hd f x y a₂ b₂ X₀ hf hxa hyb
  have i1 : InCC A 5 (scalF Wp f) := h1p k r Wp A 5 f (ContinuousLinearMap.id ℂ Wp) hfc
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI, hval]

theorem beta_zero (h3 : StCut3) (hInv : StInvGroup) (h1p : StCut1p) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hγ : IsZFrame k r D.z γ)
    (hZ : ∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0)
    (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : InCC A 5 (mc X a₁ b₁ ∘ th k r γ))
    (hc2 : InCC A 5 (mc X a₂ b₂)) :
    beta D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) = 0 := by
  have hPh : ∀ᵐ p ∂D.μSS, Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0 := by
    filter_upwards [ae_SS D] with p hp
    exact h3 hInv k r Wp D X hD hX γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI : Integrable (Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀)) D.μSS :=
    (integrable_zero _ _ _).congr (hPh.mono fun p hp => hp.symm)
  have i1 : InCC A 5 (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) := h1p k r Wp A 5 _ (ContinuousLinearMap.id ℂ Wp) hf
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI,
    integral_eq_zero_of_ae (hPh.mono fun p hp => by simp [hp]), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end
end
