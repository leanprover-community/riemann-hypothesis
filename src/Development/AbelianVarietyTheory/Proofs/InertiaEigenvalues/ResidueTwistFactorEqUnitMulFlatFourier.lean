import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGaloisStatement

section
open Matrix Formalism.IndefR.Datum
open Classical

namespace GlobalTheory

theorem addChar_inv_isPrimitive_of_isPrimitive {k : Type} [Field k] {R : Type} [CommRing R] (ψ : AddChar k R)
    (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  intro a ha h
  apply hψ (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply, neg_mul] using this

theorem sum_addChar_trace_rectMatrix_mul {k : Type} [Field k] [Fintype k] {R : Type} [CommRing R] [IsDomain R]
    (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r t : ℕ} (m : Matrix (Fin t) (Fin r) k) :
    ∑ b : Matrix (Fin r) (Fin t) k, ψ (trace (b * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r * t) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, mul_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

variable {k : Type} [Field k] {r t : ℕ}

def squareAndRectColumnsEquivWideMatrix : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k ≃ Matrix (Fin r) (Fin (r + t)) k where
  toFun p := fun i j => Fin.addCases (p.1 i) (p.2 i) j
  invFun y := (y.submatrix id (Fin.castAdd t), y.submatrix id (Fin.natAdd r))
  left_inv p := by
    ext i j
    · exact Fin.addCases_left (motive := fun _ => k) j
    · exact Fin.addCases_right (motive := fun _ => k) j
  right_inv y := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

theorem topLeftBlock_neg_eq_submatrix_castAdd (y : Matrix (Fin r) (Fin (r + t)) k) :
    topL r (-y) = -(y.submatrix id (Fin.castAdd t)) := by
  ext i j; simp only [topL]; rw [dif_pos ⟨i.2, by omega⟩]; rfl

theorem topLeftBlock_eq_submatrix_castAdd (u : Matrix (Fin (r + t)) (Fin r) k) :
    topL r u = u.submatrix (Fin.castAdd t) id := by
  ext i j; simp only [topL]; rw [dif_pos ⟨by omega, j.2⟩]; rfl

theorem lowZero_iff_submatrix_natAdd_eq_zero (u : Matrix (Fin (r + t)) (Fin r) k) :
    LowZero r u ↔ u.submatrix (Fin.natAdd r) id = 0 := by
  constructor
  · intro h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2
  · intro h i j hi _
    obtain ⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simpa using congr_fun (congr_fun h i') j

theorem trace_mul_split_castAdd_natAdd (y : Matrix (Fin r) (Fin (r + t)) k) (u : Matrix (Fin (r + t)) (Fin r) k) :
    trace (y * u) = trace (y.submatrix id (Fin.castAdd t) * u.submatrix (Fin.castAdd t) id) +
      trace (y.submatrix id (Fin.natAdd r) * u.submatrix (Fin.natAdd r) id) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]

theorem sum_GL_character_neg_det_addChar_trace (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (w : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-a).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (a * w))
      = ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
          ψ⁻¹ (trace (w * (x : Matrix (Fin r) (Fin r) k))) := by
  symm
  refine Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k))
    (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_
  · intro a ha
    rw [dif_neg, zero_mul]
    intro h
    exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩
  · intro x
    have hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det := by
      rw [neg_neg]; exact (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rw [dif_pos hx]
    have hu : hx.unit = Matrix.GeneralLinearGroup.det x := Units.ext (by simp)
    rw [hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]

end GlobalTheory

namespace GlobalTheory

theorem fourier_flatDatum_finite : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  intro k _ _ ψ ξ r n hψ hξ
  rcases lt_or_ge n r with hnr | hrn
  · refine ⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩
    have h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0 := fun y =>
      Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])
    have h2 : (topL r u).det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])
    rw [one_mul, dif_neg (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [dif_neg (by rw [h1 y]; exact not_isUnit_zero), zero_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  obtain ⟨hnorm, hGint, hGinv, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2) := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    rw [← hnorm] at this
    norm_num at this
  refine ⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩
  · refine IsIntegral.mul (IsIntegral.pow ?_ _) hGint
    rw [hq]
    exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))
  · have : q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹ := by
      rw [pow_add, mul_inv]
      field_simp
    rw [this]
    exact hGinv

  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dif_neg (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dif_neg, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

end GlobalTheory
end

section
open Matrix Formalism.IndefR.Datum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_flat_character_datum_finiteField : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  first | exact @GlobalTheory.fourier_flatDatum_finite | exact GlobalTheory.fourier_flatDatum_finite | (intros; apply GlobalTheory.fourier_flatDatum_finite <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatFourierQ

theorem unitOff_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_prod' {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_dvd {N q m : ℕ} {C : ℂ} (hq : q ∣ N) (h0 : C ≠ 0) (hC : IsIntegral ℤ C)
    (hCq : IsIntegral ℤ ((q : ℂ) ^ m * C⁻¹)) : UnitOff N C := by
  obtain ⟨d, rfl⟩ := hq
  have hint : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine ⟨h0, m, ((hint _).pow m).mul hC, ?_⟩
  have e : ((q * d : ℕ) : ℂ) ^ m * C⁻¹ = (d : ℂ) ^ m * ((q : ℂ) ^ m * C⁻¹) := by push_cast; ring
  rw [e]; exact ((hint d).pow m).mul hCq

theorem dite_prod' {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_eq_unit_mul_flat_transform : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n N : ℕ), 0 < N → (∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1 ∧ Nat.card (kP PP) ∣ N) → ∃ Gc : ℂ, UnitOff N Gc ∧ ∀ ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) ub = Gc * ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)), omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) * ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  intro D _ Q ξ ψP r n N _ hQ
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  have hloc : ∀ PP : ↥Q, ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧
      IsIntegral ℤ ((Nat.card (kP PP.1) : ℂ) ^ m * C⁻¹) ∧
      ∀ u : Matrix (Fin n) (Fin r) (kP PP.1),
        (∑ y : Matrix (Fin r) (Fin n) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C * fq PP.1 u := by
    intro PP
    letI := Ideal.Quotient.field PP.1.asIdeal
    obtain ⟨C, m, h0, h1, h2, h3⟩ :=
      GlobalTheory.T.fourier_flat_character_datum_finiteField (kP PP.1) (ψP PP.1) (ξ PP.1) r n (hQ _ PP.2).1 (hQ _ PP.2).2.1
    exact ⟨C, m, h0, h1, by rw [Nat.card_eq_fintype_card]; exact h2, h3⟩
  choose C m hC0 hCi hCm hCe using hloc
  refine ⟨(∏ PP : ↥Q, C PP)⁻¹, ?_, fun ub => ?_⟩
  · have hu : UnitOff N (∏ PP : ↥Q, C PP) :=
      unitOff_prod' _ _ fun PP _ => unitOff_of_dvd (hQ _ PP.2).2.2 (hC0 PP) (hCi PP) (hCm PP)
    obtain ⟨h0, e, h1, h2⟩ := hu
    exact ⟨inv_ne_zero h0, e, h2, by rw [inv_inv]; exact h1⟩
  · have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
      rw [← Finset.attach_eq_univ]
      unfold omegaQ
      convert dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
      intro y
      have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP),
          omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
        intro Y
        unfold omegaFlat
        convert dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
      rw [e0, Finset.attach_eq_univ]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [dif_pos PP.2, Subtype.coe_eta]
    simp only [hf, ← Finset.prod_mul_distrib]
    have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin n) (kP PP.1))))
      (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin n) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
    rw [Fintype.piFinset_univ] at hs
    rw [← hs]
    simp only [hCe]
    rw [Finset.prod_mul_distrib, hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatFourierQ
end
