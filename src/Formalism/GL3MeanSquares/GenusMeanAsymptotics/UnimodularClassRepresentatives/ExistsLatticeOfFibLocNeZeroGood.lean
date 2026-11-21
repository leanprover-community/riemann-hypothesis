import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF

section
namespace Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame

open Matrix

section Lift

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem isUnit_of_map (π : A →+* A') (hπ : Function.Surjective π)
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {u : A} (hu : IsUnit (π u)) :
    IsUnit u := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz⟩ := hπ (↑w⁻¹ : A')
  have hker : u * z - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hw, Units.mul_inv, sub_self]
  have hsq := h2 _ hker _ hker
  have h1 : u * (z * (1 - (u * z - 1))) = 1 := by linear_combination -hsq
  exact ⟨⟨u, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

theorem card_lift_unimod [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} * Nat.card (HermitianSublattices.hermSub m (RingHom.ker π)) =
      Nat.card (HermitianSublattices.entSub m m (RingHom.ker π)) *
        Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by
  classical
  have hJs : ∀ a ∈ RingHom.ker π, star a ∈ RingHom.ker π := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hπs, ha, star_zero]
  have h' : star e * (star θ - θ) = 1 := by
    have h3 := congrArg star he
    rwa [star_mul, star_sub, star_star, star_one] at h3
  have hs : star e = -e := by
    calc star e = star e * ((θ - star θ) * e) := by rw [he, mul_one]
      _ = -(star e * (star θ - θ)) * e := by ring
      _ = -e := by rw [h']; ring
  have hc : θ * e + star (θ * e) = 1 := by
    rw [star_mul, hs]
    linear_combination he
  have key := HermitianSublattices.card_lift_matrix π hπ hπs (RingHom.ker π) hJs h2 H hH H hH (fun _ => True)
    (fun _ _ _ => Iff.rfl) (fun X _ hX S hS => by
      have hXm : (Xᴴ * H * X).map π = H.map π := by
        ext i j
        have h4 := hX i j
        rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at h4
        simpa [Matrix.map_apply] using h4
      have hdetπ : IsUnit (π (Xᴴ * H * X).det) := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hXm, ← RingHom.mapMatrix_apply,
          ← RingHom.map_det]
        exact hu.map π
      rw [Matrix.det_mul, Matrix.det_mul, map_mul] at hdetπ
      have hXu : IsUnit X.det := isUnit_of_map π hπ h2 (isUnit_of_mul_isUnit_right hdetπ)
      have hXHu : IsUnit (Xᴴ * H).det := by
        rw [Matrix.det_mul, Matrix.det_conjTranspose]
        exact hXu.star.mul hu
      refine ⟨(Xᴴ * H)⁻¹ * ((θ * e) • S), ?_, ?_⟩
      · rw [HermitianSublattices.mem_entSub]
        intro i j
        rw [Matrix.mul_apply]
        refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_left _ _ ((HermitianSublattices.mem_hermSub.1 hS).2 k j)
      · have hZ : Xᴴ * H * ((Xᴴ * H)⁻¹ * ((θ * e) • S)) = (θ * e) • S := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hXHu, Matrix.one_mul]
        have hZ' : ((Xᴴ * H)⁻¹ * ((θ * e) • S))ᴴ * H * X = star (θ * e) • S := by
          have h5 : ((Xᴴ * H)⁻¹ * ((θ * e) • S))ᴴ * H * X =
              (Xᴴ * H * ((Xᴴ * H)⁻¹ * ((θ * e) • S)))ᴴ := by
            simp only [Matrix.conjTranspose_mul, hH, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc]
          rw [h5, hZ, Matrix.conjTranspose_smul, (HermitianSublattices.mem_hermSub.1 hS).1]
        rw [hZ, hZ', ← add_smul, hc, one_smul])
  have e1 : Nat.card {X : Matrix m m A // (fun _ => True) (X.map π) ∧ Xᴴ * H * X = H} =
      Nat.card {X : Matrix m m A // Xᴴ * H * X = H} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by simp)
  have e2 : Nat.card {X' : Matrix m m A' // (fun _ => True) X' ∧ X'ᴴ * (H.map π) * X' = H.map π} =
      Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun X => by simp)
  rw [e1, e2] at key
  exact key

theorem card_lift_unimod' [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) (q : ℕ)
    (hq : Nat.card (RingHom.ker π) = q ^ 2) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} =
      q ^ (Fintype.card m ^ 2) * Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by
  have h1 := card_lift_unimod π hπ hπs h2 he H hH hu
  have hJ : ∀ a ∈ RingHom.ker π, star a ∈ RingHom.ker π := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hπs, ha, star_zero]
  have hE : Nat.card (HermitianSublattices.entSub m m (RingHom.ker π)) = q ^ (2 * Fintype.card m ^ 2) := by
    rw [HermitianSublattices.card_entSub, hq, ← pow_mul]
    ring
  have hHs : Nat.card (HermitianSublattices.hermSub m (RingHom.ker π)) = q ^ (Fintype.card m ^ 2) := by
    have h3 := HermitianSublattices.card_hermSub_sq (r := m) hJ he
    rw [hE] at h3
    have e2 : q ^ (2 * Fintype.card m ^ 2) = (q ^ (Fintype.card m ^ 2)) ^ 2 := by
      rw [← pow_mul]
      ring
    rw [e2] at h3
    exact Nat.pow_left_injective two_ne_zero h3
  rw [hHs, hE] at h1
  have hq0 : 0 < q := by
    have h4 : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hq] at h4
    exact Nat.pos_of_ne_zero fun h => by simp [h] at h4
  have e3 : q ^ (2 * Fintype.card m ^ 2) = q ^ (Fintype.card m ^ 2) * q ^ (Fintype.card m ^ 2) := by
    rw [← pow_add]
    ring
  rw [e3] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 _) (by rw [h1]; ring)

end Lift

end Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
end

section
namespace Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts

open Matrix

variable {A k : Type*} [CommRing A] [StarRing A] [Field k]
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem card_conj (C : Matrix m m A) (hC : IsUnit C.det) :
    Nat.card {X : Matrix m m A // Xᴴ * (Cᴴ * C) * X = Cᴴ * C} =
      Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} := by
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  have h2 : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ hC
  have h3 : C⁻¹ᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  refine Nat.card_congr
    { toFun := fun X => ⟨C * X.1 * C⁻¹, ?_⟩
      invFun := fun Y => ⟨C⁻¹ * Y.1 * C, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hX := X.2
    calc (C * X.1 * C⁻¹)ᴴ * (C * X.1 * C⁻¹) = C⁻¹ᴴ * (X.1ᴴ * (Cᴴ * C) * X.1) * C⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (C⁻¹ᴴ * Cᴴ) * (C * C⁻¹) := by rw [hX]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, h3, Matrix.mul_one]
  · have hY := Y.2
    calc (C⁻¹ * Y.1 * C)ᴴ * (Cᴴ * C) * (C⁻¹ * Y.1 * C)
        = Cᴴ * (Y.1ᴴ * ((C⁻¹ᴴ * Cᴴ) * ((C * C⁻¹) * Y.1))) * C := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Cᴴ * C := by rw [h1, h3, Matrix.one_mul, Matrix.one_mul, hY, Matrix.mul_one]
  · intro X
    apply Subtype.ext
    show C⁻¹ * (C * X.1 * C⁻¹) * C = X.1
    calc C⁻¹ * (C * X.1 * C⁻¹) * C = (C⁻¹ * C) * X.1 * (C⁻¹ * C) := by
          simp only [Matrix.mul_assoc]
      _ = X.1 := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    apply Subtype.ext
    show C * (C⁻¹ * Y.1 * C) * C⁻¹ = Y.1
    calc C * (C⁻¹ * Y.1 * C) * C⁻¹ = (C * C⁻¹) * Y.1 * (C * C⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Y.1 := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem map_conjTranspose_mul_eq_map_transpose_mul (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (Y : Matrix m m A) :
    ((Y.map φ).map σ).transpose * Y.map φ = (Yᴴ * Y).map φ := by
  ext i j
  simp [Matrix.mul_apply, conjTranspose_apply, map_sum, hφ]

theorem card_map_equiv (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a)) :
    Nat.card {Y : Matrix m m A // Yᴴ * Y = 1} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  refine Nat.card_congr
    { toFun := fun Y => ⟨Y.1.map φ, ?_⟩
      invFun := fun X => ⟨X.1.map φ.symm, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ, Y.2]
    ext i j
    simp [Matrix.one_apply]
  · have h1 : ((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ = 1 := by
      rw [← map_conjTranspose_mul_eq_map_transpose_mul φ σ hφ]
      have : (X.1.map φ.symm).map φ = X.1 := by ext i j; simp
      rw [this, X.2]
    have h2 : (X.1.map φ.symm)ᴴ * X.1.map φ.symm
        = (((X.1.map φ.symm)ᴴ * X.1.map φ.symm).map φ).map φ.symm := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, RingEquiv.symm_apply_apply]
    rw [h2, h1]
    ext i j
    simp [Matrix.one_apply]
  · intro Y; apply Subtype.ext; ext i j; simp
  · intro X; apply Subtype.ext; ext i j; simp

theorem exists_norm [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ)
    (hq : Fintype.card k = q ^ 2) (c : k) (hc : σ c = c) : ∃ y, σ y * y = c := by
  classical
  by_cases h0 : c = 0
  · exact ⟨0, by simp [h0]⟩
  · have h := Formalism.HermitianLattices.Ext.L3.FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc
    rw [if_neg h0] at h
    have hpos : 0 < (Finset.univ.filter fun y : k => σ y * y = c).card := by
      by_contra hz
      push_neg at hz
      have hz' : (Finset.univ.filter fun y : k => σ y * y = c).card = 0 := by omega
      simp only [hz'] at h
      push_cast at h
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    exact ⟨y, (Finset.mem_filter.mp hy).2⟩

theorem card_inert [Fintype k] (φ : A ≃+* k) (σ : k ≃+* k) (hφ : ∀ a, φ (star a) = σ (φ a))
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (u : m → A) (hu : ∀ i, star (u i) = u i) (hunit : ∀ i, IsUnit (u i)) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal u * X = diagonal u} =
      Nat.card {X : Matrix m m k // (X.map σ).transpose * X = 1} := by
  have hy : ∀ i, ∃ y, σ y * y = φ (u i) := fun i =>
    exists_norm σ hσ hne q hq (φ (u i)) (by rw [← hφ, hu])
  choose y hy using hy
  set a : m → A := fun i => φ.symm (y i) with ha_def
  have ha : ∀ i, star (a i) * a i = u i := by
    intro i
    apply φ.injective
    rw [map_mul, hφ]
    simp [ha_def, hy]
  have hCC : (diagonal a)ᴴ * diagonal a = diagonal u := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact ha i
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [ha i]; exact hunit i)
  have hC : IsUnit (diagonal a).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr hau))
  rw [← hCC, card_conj (diagonal a) hC, card_map_equiv φ σ hφ]

private theorem map_conjTranspose_mul_mul_eq (φ : A →+* k) (X H : Matrix m m A) :
    (Xᴴ * H * X).map φ = (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2

private theorem map_star_eq_transpose_map_of_isHermitian (φ : A →+* k) {M : Matrix m m A} (hM : Mᴴ = M) :
    M.map (fun a => φ (star a)) = (M.map φ)ᵀ := by
  ext i j
  have h := congrFun (congrFun hM j) i
  rw [conjTranspose_apply] at h
  simp only [map_apply, transpose_apply]
  rw [h]

private theorem matrix_eq_of_map_and_map_star_eq (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    {M N : Matrix m m A} (h1 : M.map φ = N.map φ)
    (h2 : M.map (fun a => φ (star a)) = N.map (fun a => φ (star a))) : M = N := by
  ext i j
  apply hb.1
  exact Prod.ext (congrFun (congrFun h2 i) j) (congrFun (congrFun h1 i) j)

theorem card_split (φ : A →+* k) (hb : Function.Bijective fun a : A => (φ (star a), φ a))
    (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} = Nat.card (GL m k) := by
  classical
  have hdet : (H.map φ).det = φ H.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hGu : IsUnit (H.map φ).det := by
    rw [hdet]; exact hu.map φ
  have cond : ∀ X : Matrix m m A, Xᴴ * H * X = H ↔
      (X.map fun a => φ (star a))ᵀ * H.map φ * X.map φ = H.map φ := by
    intro X
    rw [← map_conjTranspose_mul_mul_eq]
    constructor
    · intro h; rw [h]
    · intro h
      apply matrix_eq_of_map_and_map_star_eq φ hb h
      have hM : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
        simp [conjTranspose_mul, hH, Matrix.mul_assoc]
      rw [map_star_eq_transpose_map_of_isHermitian φ hM, map_star_eq_transpose_map_of_isHermitian φ hH, h]
  have hP : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H}, IsUnit (X.1.map φ).det := by
    intro X
    have h := congrArg Matrix.det ((cond X.1).mp X.2)
    rw [det_mul, det_mul] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h
    exact hGu.ne_zero h.symm
  have key : ∀ X : {X : Matrix m m A // Xᴴ * H * X = H},
      (X.1.map fun a => φ (star a))ᵀ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
    intro X
    have h := (cond X.1).mp X.2
    have hu' : IsUnit (H.map φ * X.1.map φ).det := by
      rw [det_mul]; exact hGu.mul (hP X)
    calc (X.1.map fun a => φ (star a))ᵀ
        = (X.1.map fun a => φ (star a))ᵀ * (H.map φ * X.1.map φ) * (H.map φ * X.1.map φ)⁻¹ := by
          rw [Matrix.mul_assoc _ (H.map φ * X.1.map φ), Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
      _ = H.map φ * (H.map φ * X.1.map φ)⁻¹ := by
          rw [← Matrix.mul_assoc _ (H.map φ), h]
  refine Nat.card_eq_of_bijective (fun X => Matrix.nonsingInvUnit (X.1.map φ) (hP X)) ⟨?_, ?_⟩
  · intro X Y hXY
    have hPe : X.1.map φ = Y.1.map φ := congrArg Units.val hXY
    have hQe : X.1.map (fun a => φ (star a)) = Y.1.map (fun a => φ (star a)) := by
      calc X.1.map (fun a => φ (star a)) = ((X.1.map fun a => φ (star a))ᵀ)ᵀ :=
            (transpose_transpose _).symm
        _ = (H.map φ * (H.map φ * Y.1.map φ)⁻¹)ᵀ := by rw [key X, hPe]
        _ = Y.1.map (fun a => φ (star a)) := by rw [← key Y, transpose_transpose]
    exact Subtype.ext (matrix_eq_of_map_and_map_star_eq φ hb hPe hQe)
  · intro U
    let e := Equiv.ofBijective _ hb
    let X : Matrix m m A := Matrix.of fun i j =>
      e.symm ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j)
    have hX : ∀ i j, (φ (star (X i j)), φ (X i j)) =
        ((H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ i j, (↑U : Matrix m m k) i j) :=
      fun i j => e.apply_symm_apply _
    have hXP : X.map φ = (↑U : Matrix m m k) := by
      ext i j; exact congrArg Prod.snd (hX i j)
    have hXQ : X.map (fun a => φ (star a)) = (H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹)ᵀ := by
      ext i j; exact congrArg Prod.fst (hX i j)
    have hc : Xᴴ * H * X = H := by
      rw [cond, hXP, hXQ, transpose_transpose]
      calc H.map φ * (↑U⁻¹ : Matrix m m k) * (H.map φ)⁻¹ * H.map φ * (↑U : Matrix m m k)
          = H.map φ * (↑U⁻¹ : Matrix m m k) * ((H.map φ)⁻¹ * H.map φ) * (↑U : Matrix m m k) := by
            simp only [Matrix.mul_assoc]
        _ = H.map φ := by
            rw [Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul,
              Matrix.mul_one]
    refine ⟨⟨X, hc⟩, ?_⟩
    apply Units.ext
    exact hXP

end Formalism.HermitianLattices.Ext.L3.UnitaryNormCounts
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

def isoCount (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) : ℕ :=
  Nat.card {X : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    Xᴴ * g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X = g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))}

theorem map_mk_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) :
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = gᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rfl

theorem isUnit_mk {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) δ) := by
  have h2 : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := Ideal.sup_pow_eq_top hδ
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := h2
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hq : Ideal.Quotient.mk (extP K 𝔭 ^ N) (δ * a) = Ideal.Quotient.mk (extP K 𝔭 ^ N) 1 := by
    rw [Ideal.Quotient.eq]
    have hza : δ * a - 1 = -z := by
      rw [← hyz]
      ring
    rw [hza]
    exact neg_mem hz
  rw [map_mul, map_one] at hq
  exact isUnit_iff_exists_inv.mpr ⟨_, hq⟩

theorem isoCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) {k : ℕ} (hk : 1 ≤ k) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (m ^ 2) * isoCount 𝔭 k g := by
  have hF := hFF.out
  have := finite_quot (K := K) h𝔭 (k + 1)
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ (k + 1)
  have he' : (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ -
      star (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) θ)) * Ideal.Quotient.mk _ e = 1 := by
    rw [star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))]
    exact Ideal.Quotient.eq.2 he
  have h := FirstPropositionFrame.card_lift_unimod' (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k)
    (by
      intro a ha b hb
      rw [ker_piQ] at ha hb
      exact mul_eq_zero_idQ (by omega) ha hb) he'
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1))))
    (by rw [map_mk_conjTranspose, hg])
    (by
      have : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).det =
          Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) g.det := (RingHom.map_det _ g).symm
      rw [this]
      exact isUnit_mk hdet _)
    (Ideal.absNorm 𝔭) (card_ker_piQ hK hF h𝔭 k)
  rw [Fintype.card_fin] at h
  have hm : (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))).map (piQ K 𝔭 k) =
      g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by
    ext i j
    rfl
  rw [hm] at h
  exact h

theorem isoCount_eq_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (g : Matrix (Fin m) (Fin m) (𝓞 K)) (hg : gᴴ = g)
    (hdet : Ideal.span {g.det} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    isoCount 𝔭 (k + 1) g = Ideal.absNorm 𝔭 ^ (k * m ^ 2) * isoCount 𝔭 1 g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [isoCount_succ hK h𝔭 g hg hdet (by omega), ih, ← mul_assoc, ← pow_add]
    congr 2
    ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem isoCount_one_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - (-(Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  have e1 : extP K 𝔭 ^ 1 = P := by
    rw [pow_one]
    exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP
      (by rw [← conjIdeal_eq_comap]; exact hc) hθ
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]
  have hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x := NormResidues.sigHom_sigHom P hc
  have hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x := by
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [NormResidues.sigEquiv_mk] at h
    exact Ideal.Quotient.eq.1 h.symm
  have h1 := UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]
      rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))
    (by
      intro i
      rw [star_mk, star_def, hu])
    (fun i => isUnit_mk (hunit i) 1)
  unfold isoCount
  rw [diagonal_map (map_zero _), h1]
  exact card_unitary_fin _ hσ hne _ hq m

theorem isoCount_one_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - ((Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have e1 : extP K 𝔭 ^ 1 ≤ P := by
    rw [pow_one]
    exact Ideal.map_comap_le
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := finite_quot (K := K) h𝔭 1
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]
  have hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 =>
      (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a) := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro y
      obtain ⟨z, hz⟩ := NormResidues.pairHom_surjective hP hc y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      rw [← hz, NormResidues.pairHom_apply]
      show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _
      rw [star_mk]
      rfl
    · rw [absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]
      apply le_of_eq
      ring
  have h1 := UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb
    ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)))
    (by
      rw [map_mk_conjTranspose, diagonal_conjTranspose]
      congr 2
      funext i
      exact hu i)
    (by
      rw [diagonal_map (map_zero _), det_diagonal]
      exact Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
        (fun i _ => isUnit_mk (hunit i) 1))
  unfold isoCount
  rw [h1]
  exact card_GL_fin _ hq m

theorem isoCount_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, if_pos hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, if_neg hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]

theorem isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.OrthogonalBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem sup_eq_top_of_mem_hcompl (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hu' := (Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu
  have huQ : u ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q := le_trans le_sup_right hle
  have hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.map_le_iff_le_comap.1 hext
  have hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  haveI := hQ.isPrime
  have heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ
  rcases (comap_eq_comap_iff hK hF hP hQ).1 heq with h | h
  · exact hu'.1 (h ▸ huQ)
  · exact hu'.2 (h ▸ huQ)

private theorem isUnitIn_mul' {S : Subring K} {a b : K} (ha : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S a)
    (hb : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S b) : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem exists_orth_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (u : Fin (finrank K V) → 𝓞 K), (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
      (∀ i j, algebraMap (𝓞 K) K (diagonal u i j) = h (b i) (b j)) ∧
      (∀ i, conjO K (u i) = u i) ∧ ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  have hSD := Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hP.isPrime hU
  have hdd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hd x hx0 (Classical.arbitrary (NumberField.InfinitePlace K)).embedding
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl 0 this
  obtain ⟨x, hxM, hxo, hxu⟩ := Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame
    (Formalism.HermitianLattices.Ext.L3.WA.isHermSemilocal_locRing hK hP)
    (Formalism.HermitianLattices.Ext.L3.LocF.locRing_local hP.isPrime) hs hdd hSD
  have hx' : ∀ i, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • x i ∈ L := fun i => hxM i
  choose s hsP hsL using hx'
  set b0 : Fin (finrank K V) → V := fun i => algebraMap (𝓞 K) K (s i) • x i with hb0
  have hb0L : ∀ i, b0 i ∈ L := by
    intro i
    simp only [hb0, algebraMap_smul]
    exact hsL i
  have hbb : ∀ i j, h (b0 i) (b0 j) =
      star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s j) * h (x i) (x j) := by
    intro i j
    simp only [hb0, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply]
    ring
  have hunit : ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn (Formalism.HermitianLattices.Ext.L3.WA.locRing P) (h (b0 i) (b0 i)) := by
    intro i
    have hσ := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (s i)).2 (hsP i)
    have hσs := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (conjO K (s i))).2
      (Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl (hsP i))
    rw [hbb]
    exact isUnitIn_mul' (isUnitIn_mul' hσs hσ) (hxu i)
  have horth : ∀ i j, i ≠ j → h (b0 i) (b0 j) = 0 := by
    intro i j hij
    rw [hbb, hxo i j hij, mul_zero]
  have hint : ∀ i, h (b0 i) (b0 i) ∈ (1 : Submodule (𝓞 K) K) := fun i => hLi _ (hb0L i) _ (hb0L i)
  choose u hu using fun i => Submodule.mem_one.1 (hint i)
  have huP : ∀ i, u i ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    intro i
    refine (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (u i)).1 ?_
    rw [hu i]
    exact hunit i
  have hli : LinearIndependent K b0 := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have := congrArg (h (b0 i)) hg
    rw [map_sum, map_zero, Finset.sum_eq_single i] at this
    · rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (hunit i).1
    · intro j _ hji
      rw [map_smul, horth i j (Ne.symm hji), smul_zero]
    · intro hi'
      exact absurd hi hi'
  have htop : ⊤ ≤ Submodule.span K (Set.range b0) :=
    (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])).ge
  let b := Basis.mk hli htop
  have hb : ⇑b = b0 := Basis.coe_mk hli htop
  refine ⟨b, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hb0L i
  · rw [hb, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    apply le_antisymm
    · rintro y ⟨t, ht, hy⟩
      exact ⟨t, ht, (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb0L i)) hy⟩
    · rintro y ⟨t, ht, hy⟩
      have hz : t • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b0)) := by
        rw [← b.sum_repr (t • y)]
        refine Submodule.sum_mem _ fun i _ => ?_
        refine ⟨u i, huP i, ?_⟩
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hLi _ (hb0L i) _ hy)
        have hrep : h (b0 i) (t • y) = b.repr (t • y) i * h (b0 i) (b0 i) := by
          conv_lhs => rw [← b.sum_repr (t • y)]
          rw [map_sum, Finset.sum_eq_single i]
          · rw [map_smul, smul_eq_mul, hb]
          · intro j _ hji
            rw [map_smul, hb, horth i j (Ne.symm hji), smul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        have key : u i • (b.repr (t • y) i • b i) = a • b0 i := by
          rw [← algebraMap_smul K (u i), smul_smul, hu i, mul_comm, ← hrep, ← ha, algebraMap_smul, hb]
        rw [key]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨t', ht', hy'⟩ := hz
      exact ⟨t' * t, mul_mem ht' ht, by rw [mul_smul]; exact hy'⟩
  · intro i j
    rw [hb, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hu i
    · rw [map_zero, horth i j hij]
  · intro i
    apply IsFractionRing.injective (𝓞 K) K
    have h1 : algebraMap (𝓞 K) K (conjO K (u i)) = star (algebraMap (𝓞 K) K (u i)) := rfl
    rw [h1, hu i, ← starRingEnd_apply]
    exact hs.eq (b0 i) (b0 i)
  · intro i
    exact sup_eq_top_of_mem_hcompl hK hF hP (huP i)

end Formalism.HermitianLattices.Ext.L3.OrthogonalBases
end
end

section
open NumberField Module Matrix Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_eq_of_bridge [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin (finrank K V) → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤)
    (hbr : ∀ k, akCount h L 𝔭 k = isoCount 𝔭 k (diagonal u)) :
    alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
      (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
        (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast this
  unfold alphaL
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hbr, isoCount_diag hK h𝔭 u hu hunit j, eq_div_iff (pow_ne_zero _ hN)]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_of_vd_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, u, -, hb, hH, hu, hunit⟩ := OrthogonalBases.exists_orth_basis hK hF hs hd hL hLi h𝔭 hv
  exact IsotropicCounts.alphaL_eq_of_bridge hK h𝔭 u hu hunit fun k => integralBasisSpans.akCount_eq h h𝔭 b hb hH k

theorem alphaStd_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (m : ℕ) : 0 < alphaStd K 𝔭 m := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (1 : ℝ) < Ideal.absNorm 𝔭 := by
    have : 1 < Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  unfold alphaStd
  apply Finset.prod_pos
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hN (by omega)
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by linarith) _
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h]
  · rw [one_pow, one_mul]
    linarith
  · rcases neg_one_pow_eq_or ℝ j with h' | h' <;> rw [h'] <;> linarith

theorem localMassFactor_of_valuation_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : lamP h L 𝔭 = 1 := by
  unfold lamP
  rw [hv, mul_zero, pow_zero, mul_one, alphaL_of_vd_zero hK hF hs hd hL hLi h𝔭 hv]
  exact div_self (alphaStd_pos hK hF h𝔭 _).ne'

theorem lamG_eq_one_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) : lamG F h I = 1 := by
  unfold lamG
  have hd := isTotPosDef_of_ortho hK hs hI
  have hL := isLattice_of_ortho hI
  have hLi := isIntegralLat_of_ortho hI
  have : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h I 𝔭.1 = 1 := by
    intro 𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2
    rw [← hP𝔭]
    exact (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mp (isUnimodularAt_of_ortho hK hs hI P hP)
  simp only [this, tprod_one]

end Formalism.HermitianLattices.Ext.L3
end
end

section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.UnimodularLocalization

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nondegenerate (hd : IsTotPosDef h) : h.Nondegenerate := by
  have hne : ∀ v : V, v ≠ 0 → h v v ≠ 0 := by
    intro v hv e
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd v hv φ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  constructor
  · intro x hx
    by_contra h0
    exact hne x h0 (hx x)
  · intro x hx
    by_contra h0
    exact hne x h0 (hx x)

theorem loc_eq_loc_adjoin_cut (S : VecSplit h h') {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.loc (K := K) P B)
    (hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P) :
    Formalism.HermitianLatticesTheory.loc (K := K) P B = Formalism.HermitianLatticesTheory.loc (K := K) P (S.adjoin (S.cut B)) := by
  obtain ⟨hloc, -⟩ := Formalism.HermitianLatticesTheory.locBasic (𝓞 K) K V Formalism.HermitianLatticesTheory.genusCovol_hinj
  have hidem : Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.loc (K := K) P B) = Formalism.HermitianLatticesTheory.loc (K := K) P B :=
    (hloc P hP B B).2.2.1
  apply le_antisymm
  · intro b hb
    obtain ⟨c, a, rfl⟩ := S.cover b
    have hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
      have h1 := LocalizedFibreSets.form_mem_locR hBi P hx hb
      rw [S.h_x₀_comb] at h1
      have := mul_mem_locR P h1 hn'
      rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this
    rw [S.comb_mem_loc_adjoin_iff]
    refine ⟨hc, ?_⟩
    have h2 : S.ι a ∈ Formalism.HermitianLatticesTheory.loc (K := K) P B := by
      have h3 := Submodule.sub_mem _ hb (LocalizedFibreSets.smul_mem_of_loc_eq hidem hc hx)
      rwa [add_sub_cancel_left] at h3
    obtain ⟨s, hs', h4⟩ := h2
    refine ⟨s, hs', ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower]
    exact h4
  · rw [← hidem]
    apply (hloc P hP _ _).2.1
    unfold VecSplit.adjoin
    refine sup_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hx
    · rw [Submodule.map_le_iff_le_comap]
      intro a ha
      exact (hloc P hP B B).1 ha

theorem unimod_of_unimod_adjoin (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L')) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hU ⊢
  ext a
  have h1 := LocalizedFibreSets.comb_mem_dualAt_iff hs S p L' 0 a
  rw [hU, S.comb_mem_loc_adjoin_iff, zero_mul] at h1
  constructor
  · intro ha
    exact (h1.mpr ⟨Submodule.zero_mem _, ha⟩).2
  · intro ha
    exact (h1.mp ⟨Submodule.zero_mem _, ha⟩).2

theorem isIntegralLat_cut (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S.cut B) := by
  intro x hx y hy
  rw [← S.isom]
  exact hBi _ hx _ hy

theorem algebraMap_smul_K (t : 𝓞 F) (c : K) :
    algebraMap (𝓞 F) (𝓞 K) t • c = algebraMap F K (t : F) * c := by
  rw [Algebra.smul_def]
  rfl

theorem locR_eq_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.locR (K := K) P =
      locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (1 : Submodule (𝓞 K) K) :=
  (locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)).symm

theorem inv_mem_locF_one {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : n ∉ 𝔭) : (algebraMap F K (n : F))⁻¹ ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  rw [LocF.mem_locF_iff h𝔭.isPrime]
  refine ⟨n, hn, ?_⟩
  rw [algebraMap_smul_K, mul_inv_cancel₀]
  · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · rw [map_ne_zero]
    exact fun e => hn0 (RingOfIntegers.ext e)

theorem vd_cut_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvB : vd h B 𝔭 = 0) (hvn : vF 𝔭 n = 0) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = 0 := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact S.hx₀ (by rw [hn]; simp)
  rw [← isUnimodularAt_iff_vd hK hF hs hd hB hBi hP] at hvB
  rw [← isUnimodularAt_iff_vd hK hF (S.isSymm hs) (S.isTotPosDef hd) (StabilizerLattices.isLattice_cut S hB)
    (isIntegralLat_cut S hBi) hP]
  apply unimod_of_unimod_adjoin hs S
  rw [locF_eq_loc hK hF hP] at hx
  have hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
    rw [locR_eq_locF hK hF hP, hn]
    exact inv_mem_locF_one h𝔭 hn0 (LocalizedFibreSets.notMem_of_vF_zero h𝔭 hn0 hvn)
  rwa [← isUnimodularAt_of_loc_eq P (loc_eq_loc_adjoin_cut S hP.isPrime hBi hx hn')]

theorem exists_unimod_through (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L) {x₀ : V}
    (hx : h x₀ x₀ ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ B : Submodule (𝓞 K) V, Submodule.IsLattice K B ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h B ∧
      Formalism.HermitianLatticesTheory.IsUnimodularAt h P B ∧ x₀ ∈ B := by
  obtain ⟨hanti, hbi, hsup, hint, -⟩ := Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have DL := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate hd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨hloc, -⟩ := Formalism.HermitianLatticesTheory.locBasic (𝓞 K) K V Formalism.HermitianLatticesTheory.genusCovol_hinj
  set X : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {x₀} with hX
  have hxX : x₀ ∈ X := Submodule.mem_span_singleton_self x₀
  have hXX : X ≤ Formalism.HermitianLatticesTheory.dual h X := by
    intro y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_dual]
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [LocalizedFibreSets.form_smul_smul]
    exact Submodule.smul_mem _ _ hx
  have hLd : L ≤ Formalism.HermitianLatticesTheory.dual h L := (hint L).mp hLi
  set B : Submodule (𝓞 K) V := (L ⊓ Formalism.HermitianLatticesTheory.dual h X) ⊔ X with hB
  have hBfg : B.FG := (hL.fg.of_le inf_le_left).sup (Submodule.fg_span_singleton x₀)
  have hBl : Submodule.IsLattice K B := by
    refine ⟨hBfg, ?_⟩
    rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro v hv
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (h x₀ v)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [map_ne_zero_iff _ Formalism.HermitianLatticesTheory.genusCovol_hinj]
      exact nonZeroDivisors.ne_zero hb
    have h1 : b • v ∈ B := by
      apply Submodule.mem_sup_left
      refine ⟨L.smul_mem b hv, ?_⟩
      change b • v ∈ Formalism.HermitianLatticesTheory.dual h X
      rw [Formalism.HermitianLatticesTheory.isomAct_mem_dual]
      intro z hz
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [LocalizedFibreSets.form_smul_smul, mul_smul]
      apply Submodule.smul_mem
      rw [← e, Algebra.smul_def, mul_div_cancel₀ _ hb0]
      exact Submodule.mem_one.mpr ⟨a, rfl⟩
    have h2 : (algebraMap (𝓞 K) K b)⁻¹ • (b • v) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← algebraMap_smul K b v, smul_smul, inv_mul_cancel₀ hb0, one_smul] at h2
  have lat2 : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h L ⊔ X) := by
    refine ⟨(DL L hL).1.fg.sup (Submodule.fg_span_singleton x₀), ?_⟩
    rw [eq_top_iff, ← (DL L hL).1.span_eq_top]
    exact Submodule.span_mono (show Formalism.HermitianLatticesTheory.dual h L ≤ Formalism.HermitianLatticesTheory.dual h L ⊔ X from le_sup_left)
  have e1 : L ⊓ Formalism.HermitianLatticesTheory.dual h X = Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.dual h L ⊔ X) := by
    rw [hsup, (DL L hL).2.1]
  have e2 : Formalism.HermitianLatticesTheory.dual h (L ⊓ Formalism.HermitianLatticesTheory.dual h X) = Formalism.HermitianLatticesTheory.dual h L ⊔ X := by
    rw [e1, (DL _ lat2).2.1]
  have e3 : Formalism.HermitianLatticesTheory.dual h B = (Formalism.HermitianLatticesTheory.dual h L ⊔ X) ⊓ Formalism.HermitianLatticesTheory.dual h X := by
    rw [hB, hsup, e2]
  refine ⟨B, hBl, ?_, ?_, Submodule.mem_sup_right hxX⟩
  · rw [hint, e3]
    refine sup_le (le_inf (inf_le_left.trans (hLd.trans le_sup_left)) inf_le_right)
      (le_inf le_sup_right hXX)
  · have LDB := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range B hBfg).1 P hP
    have LDL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).1 P hP
    have e4 : Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h L) = Formalism.HermitianLatticesTheory.loc (K := K) P L := by
      rw [LDL.1, ← LDL.2]
      exact hU
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
    rw [LDB.2, ← LDB.1, e3, (hloc P hP _ _).2.2.2.1, (hloc P hP _ _).2.2.2.2, e4, hB,
      (hloc P hP _ _).2.2.2.2, (hloc P hP _ _).2.2.2.1, sup_comm, sup_inf_assoc_of_le, sup_comm]
    exact (hloc P hP _ _).2.1 hXX

theorem vd_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : vd h (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 = vd h L 𝔭 := by
  have e : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g L) = discrIdeal h L := by
    unfold discrIdeal
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, e⟩
      refine ⟨fun i => g.symm (x i), fun i => (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g L _).mp (hx i), ?_⟩
      rw [e]
      congr 1
      ext i j
      exact (SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg) _ _).symm
    · rintro ⟨x, hx, e⟩
      refine ⟨fun i => g (x i), fun i => StabilizerLattices.apply_mem_gmap g (hx i), ?_⟩
      rw [e]
      congr 1
      ext i j
      exact (SplitBAux.isom_apply hg _ _).symm
  unfold vd
  rw [e]

theorem isIntegralLat_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) :=
  ((Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g hg L).2.2.1).mpr hLi

theorem exists_of_fibLoc_ne_zero (S : VecSplit h h') {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) ∧
      locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) = locF 𝔭 T := by
  have hne : Nonempty {Λ : Submodule (𝓞 K) V // locF 𝔭 Λ = Λ ∧
      (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
      S.cut Λ = locF 𝔭 T} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hT Nat.card_of_isEmpty
  obtain ⟨Λ, -, ⟨g, hg, rfl⟩, hx, hc⟩ := hne
  rw [LocalizedFibreSets.gmap_locF] at hx hc
  exact ⟨g, hg, hx, by rw [← LocalizedFibreSets.cut_locF, hc]⟩

theorem fibLoc_locF (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : fibLoc S L 𝔭 (locF 𝔭 T) = fibLoc S L 𝔭 T := by
  unfold fibLoc
  rw [LocF.locF_idem]

theorem fibLoc_congr (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    fibLoc S L 𝔭 T = fibLoc S L 𝔭 T' := by
  rw [← fibLoc_locF S L 𝔭 T, e, fibLoc_locF]

theorem localFactor_localField (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h (locF 𝔭 L) 𝔭 = lamP h L 𝔭 := by
  have e : alphaL h (locF 𝔭 L) 𝔭 = alphaL h L 𝔭 := by
    unfold alphaL
    congr 1
    ext k
    rw [akCount_locF hF h L 𝔭 h𝔭]
  unfold lamP
  rw [vd_locF hK hF hs hd hL hLi h𝔭, e]

theorem exists_lattice_of_fibLoc_ne_zero (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, hg, -, e⟩ := exists_of_fibLoc_ne_zero S hT
  exact ⟨_, StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL),
    isIntegralLat_cut S (isIntegralLat_gmap hg hLi), e⟩

theorem exists_lattice_of_fibLoc_ne_zero_good (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0)
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      vd h' C 𝔭 = 0 ∧ locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, hg, hx, e⟩ := exists_of_fibLoc_ne_zero S hT
  exact ⟨_, StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL),
    isIntegralLat_cut S (isIntegralLat_gmap hg hLi),
    vd_cut_eq_zero hK hF hs hd S (LocalizedFibreSets.isLattice_gmap g hL) (isIntegralLat_gmap hg hLi) h𝔭 hn
      (by rw [vd_gmap hg, hvL]) hvn hx, e⟩

theorem exists_unimod_lattice_good (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      vd h' C 𝔭 = 0 := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hU := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mpr hvL
  have hx : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hn]
    exact Submodule.mem_one.mpr ⟨algebraMap (𝓞 F) (𝓞 K) n, rfl⟩
  obtain ⟨B, hB, hBi, hBU, hxB⟩ := exists_unimod_through hs hd hL hLi hP.isPrime hU hx
  exact ⟨_, StabilizerLattices.isLattice_cut S hB, isIntegralLat_cut S hBi,
    vd_cut_eq_zero hK hF hs hd S hB hBi h𝔭 hn
      ((isUnimodularAt_iff_vd hK hF hs hd hB hBi hP).mp hBU) hvn (LocF.le_locF _ _ hxB)⟩

end Formalism.HermitianLattices.Ext.L3.UnimodularLocalization
end
end
