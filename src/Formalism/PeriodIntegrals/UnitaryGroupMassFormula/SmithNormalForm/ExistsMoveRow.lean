import Mathlib
import Formalism.PeriodIntegrals.SmithMat

section
namespace PI.SmithWork

open Matrix

variable {R : Type*} [CommRing R]

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Eqv (A B : Matrix ι ι R) : Prop :=
  ∃ U V : Matrix ι ι R, IsUnit U ∧ IsUnit V ∧ U * A * V = B

theorem Eqv.refl (A : Matrix ι ι R) : Eqv A A :=
  ⟨1, 1, isUnit_one, isUnit_one, by simp⟩

theorem Eqv.trans {A B C : Matrix ι ι R} (h₁ : Eqv A B) (h₂ : Eqv B C) : Eqv A C := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h₁
  obtain ⟨U', V', hU', hV', rfl⟩ := h₂
  exact ⟨U' * U, V * V', hU'.mul hU, hV.mul hV', by simp only [Matrix.mul_assoc]⟩

theorem Eqv.mul_left {A B U : Matrix ι ι R} (h : Eqv A B) (hU : IsUnit U) : Eqv A (U * B) :=
  h.trans ⟨U, 1, hU, isUnit_one, by simp⟩

theorem Eqv.mul_right {A B V : Matrix ι ι R} (h : Eqv A B) (hV : IsUnit V) : Eqv A (B * V) :=
  h.trans ⟨1, V, isUnit_one, hV, by simp⟩

theorem isUnit_of_mul_eq_one {A B : Matrix ι ι R} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).2 (Matrix.isUnit_det_of_right_inverse h)

theorem isUnit_one_add_vecMulVec (u v : ι → R) (h : v ⬝ᵥ u = 0) :
    IsUnit (1 + vecMulVec u v) := by
  have hT : vecMulVec u v * vecMulVec u v = 0 := by
    rw [vecMulVec_mul_vecMulVec, h]; ext; simp [vecMulVec_apply]
  apply isUnit_of_mul_eq_one (B := 1 - vecMulVec u v)
  rw [add_mul, mul_sub, mul_sub, hT]; simp

theorem addRow_apply (t : ι → R) (i : ι) (B : Matrix ι ι R) (a c : ι) :
    ((1 + vecMulVec t (Pi.single i 1)) * B) a c = B a c + t a * B i c := by
  rw [add_mul, one_mul, vecMulVec_mul, single_one_vecMul]
  simp [vecMulVec_apply]

theorem addCol_apply (s : ι → R) (i : ι) (B : Matrix ι ι R) (a c : ι) :
    (B * (1 + vecMulVec (Pi.single i 1) s)) a c = B a c + B a i * s c := by
  rw [mul_add, mul_one, mul_vecMulVec, mulVec_single_one]
  simp [vecMulVec_apply]

def two (i j : ι) (p q r s : R) : Matrix ι ι R := fun a =>
  if a = i then p • Pi.single i 1 + q • Pi.single j 1
  else if a = j then r • Pi.single i 1 + s • Pi.single j 1
  else Pi.single a 1

end General

section Block

variable {n : ℕ}

def blk (b : R) (D : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun a c => Fin.cases (Fin.cases b (fun _ => 0) c) (fun i => Fin.cases 0 (fun k => D i k) c) a

@[simp] theorem blk_zero_zero (b : R) (D : Matrix (Fin n) (Fin n) R) : blk b D 0 0 = b := rfl
@[simp] theorem blk_zero_succ (b : R) (D : Matrix (Fin n) (Fin n) R) (k : Fin n) :
    blk b D 0 k.succ = 0 := rfl
@[simp] theorem blk_succ_zero (b : R) (D : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    blk b D i.succ 0 = 0 := rfl
@[simp] theorem blk_succ_succ (b : R) (D : Matrix (Fin n) (Fin n) R) (i k : Fin n) :
    blk b D i.succ k.succ = D i k := rfl

theorem blk_mul (b b' : R) (D D' : Matrix (Fin n) (Fin n) R) :
    blk b D * blk b' D' = blk (b * b') (D * D') := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blk_one : blk (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem isUnit_blk_one {U : Matrix (Fin n) (Fin n) R} (hU : IsUnit U) : IsUnit (blk 1 U) := by
  obtain ⟨u, rfl⟩ := hU
  apply isUnit_of_mul_eq_one (B := blk 1 (↑u⁻¹ : Matrix (Fin n) (Fin n) R))
  rw [blk_mul, one_mul, Units.mul_inv, blk_one]

theorem eq_blk (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hr : ∀ k : Fin n, B 0 k.succ = 0)
    (hc : ∀ i : Fin n, B i.succ 0 = 0) :
    B = blk (B 0 0) (B.submatrix Fin.succ Fin.succ) := by
  ext a c
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;>
    simp [hr, hc]

theorem Eqv.blk {D D' : Matrix (Fin n) (Fin n) R} (h : Eqv D D') (b : R) :
    Eqv (blk b D) (blk b D') := by
  obtain ⟨U, V, hU, hV, rfl⟩ := h
  exact ⟨_, _, isUnit_blk_one hU, isUnit_blk_one hV, by simp [blk_mul]⟩

end Block

end PI.SmithWork
end

section
namespace PI.SmithWork

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sum_pairSingle_mul_eq_ite (i j : ι) (hij : i ≠ j) (x y z w : R) (p : ι) (v : ι → R) :
    ∑ r, (if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i z + Pi.single j w else Pi.single p 1 : ι → R) r * v r =
      if p = i then x * v i + y * v j else if p = j then z * v i + w * v j else v p := by
  by_cases hpi : p = i
  · simp [hpi, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
  · by_cases hpj : p = j
    · simp [hpi, hpj, Ne.symm hij, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]
    · simp [hpi, hpj, Pi.single_apply, ite_mul]

private theorem unit_lemma' (i j : ι) (hij : i ≠ j) (x y a' b' : R) (key : x * a' + y * b' = 1) :
    IsUnit (Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) := by
  have h : (Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * (Matrix.of fun p => if p = i then Pi.single i a' + Pi.single j (-y)
      else if p = j then Pi.single i b' + Pi.single j x else Pi.single p 1 : Matrix ι ι R) = 1 := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [sum_pairSingle_mul_eq_ite i j hij x y (-b') a' p, Matrix.one_apply]
    by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;> by_cases hqj : q = j <;>
      simp_all [Pi.single_apply, Ne.symm hij] <;>
      first | ring1 | linear_combination key | (intro h; exact hqi h.symm) | (intro h; exact hqj h.symm) | (simp only [@eq_comm _ q p])
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem exists_row_gcd (B : Matrix ι ι R) (i j c : ι) (hij : i ≠ j) (h0 : B i c ≠ 0) :
    ∃ U : Matrix ι ι R, IsUnit U ∧ (U * B) i c ∣ B i c ∧ (U * B) i c ∣ B j c := by
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (Ideal.span {B i c, B j c})).principal
  have ha : B i c ∈ (Submodule.span R {d} : Ideal R) := by
    rw [← hd]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hb : B j c ∈ (Submodule.span R {d} : Ideal R) := by
    rw [← hd]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hdm : d ∈ Ideal.span {B i c, B j c} := by
    rw [hd]; exact Submodule.mem_span_singleton_self d
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hb
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hdm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha'
    exact h0 ha'.symm
  have key : x * a' + y * b' = 1 := by
    apply mul_right_cancel₀ hd0
    rw [one_mul, add_mul, mul_assoc, mul_assoc, ha', hb', hxy]
  have hUB : ((Matrix.of fun p => if p = i then Pi.single i x + Pi.single j y
      else if p = j then Pi.single i (-b') + Pi.single j a' else Pi.single p 1 : Matrix ι ι R) * B) i c = d := by
    simp [Matrix.mul_apply, Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul, hxy]
  refine ⟨_, unit_lemma' i j hij x y a' b' key, ?_, ?_⟩
  · rw [hUB]; exact ⟨a', by rw [← ha', mul_comm]⟩
  · rw [hUB]; exact ⟨b', by rw [← hb', mul_comm]⟩

theorem exists_col_gcd (B : Matrix ι ι R) (i j a : ι) (hij : i ≠ j) (h0 : B a i ≠ 0) :
    ∃ V : Matrix ι ι R, IsUnit V ∧ (B * V) a i ∣ B a i ∧ (B * V) a i ∣ B a j := by
  obtain ⟨U, hU, h1, h2⟩ := exists_row_gcd Bᵀ i j a hij h0
  have e : (B * Uᵀ) a i = (U * Bᵀ) i a := by
    have h := congrFun (congrFun (Matrix.transpose_mul U Bᵀ) a) i
    rw [Matrix.transpose_transpose] at h
    rw [← h]
    rfl
  refine ⟨Uᵀ, ?_, ?_, ?_⟩
  · refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hU
  · rw [e]; exact h1
  · rw [e]; exact h2

theorem exists_move_row (B : Matrix ι ι R) (i j : ι) :
    ∃ U : Matrix ι ι R, IsUnit U ∧ ∀ c, (U * B) i c = B j c := by
  refine ⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun c => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]
    exact (Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)
  · simp [PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Equiv.swap_apply_left]

theorem exists_move_col (B : Matrix ι ι R) (i j : ι) :
    ∃ V : Matrix ι ι R, IsUnit V ∧ ∀ a, (B * V) a i = B a j := by
  refine ⟨(Equiv.swap i j).toPEquiv.toMatrix, ?_, fun a => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]
    exact (Equiv.Perm.sign _).isUnit.map (Int.castRingHom R)
  · simp [PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply, Equiv.swap_apply_left]

end General

theorem exists_blk {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    ∃ (b : R) (D : Matrix (Fin n) (Fin n) R), Eqv A (blk b D) ∧ ∀ i k, b ∣ D i k := by
  by_cases hA : A = 0
  · refine ⟨0, 0, ?_, fun i k => by simp⟩
    have h0 : blk (0 : R) (0 : Matrix (Fin n) (Fin n) R) = A := by
      rw [hA]
      ext a c
      refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun k => ?_) c <;> simp
    rw [h0]
    exact Eqv.refl A
  let S : Set R := {r | r ≠ 0 ∧ ∃ B, Eqv A B ∧ B 0 0 = r}
  have hS : S.Nonempty := by
    obtain ⟨a, c, hac⟩ : ∃ a c, A a c ≠ 0 := by
      by_contra h
      push Not at h
      exact hA (by ext a c; simpa using h a c)
    obtain ⟨U, hU, h1⟩ := exists_move_row A 0 a
    obtain ⟨V, hV, h2⟩ := exists_move_col (U * A) 0 c
    exact ⟨A a c, hac, U * A * V, ((Eqv.refl A).mul_left hU).mul_right hV, by rw [h2, h1]⟩
  obtain ⟨b, ⟨hb0, B, hAB, hB⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := R)).has_min S hS
  have key : ∀ g ∈ S, g ∣ b → b ∣ g := by
    rintro g hg ⟨x, hx⟩
    by_cases hxu : IsUnit x
    · obtain ⟨u, rfl⟩ := hxu
      exact ⟨↑u⁻¹, by rw [hx]; simp [mul_assoc]⟩
    · exact absurd ⟨hg.1, x, hxu, hx⟩ (hmin g hg)
  have hcol : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B j 0 := by
    intro B hAB hB j
    by_cases hj : j = 0
    · rw [hj, hB]
    obtain ⟨U, hU, h1, h2⟩ := exists_row_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)
    rw [hB] at h1
    have hmem : (U * B) 0 0 ∈ S :=
      ⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), U * B, hAB.mul_left hU, rfl⟩
    exact (key _ hmem h1).trans h2
  have hrow : ∀ B, Eqv A B → B 0 0 = b → ∀ j, b ∣ B 0 j := by
    intro B hAB hB j
    by_cases hj : j = 0
    · rw [hj, hB]
    obtain ⟨V, hV, h1, h2⟩ := exists_col_gcd B 0 j 0 (Ne.symm hj) (by rw [hB]; exact hb0)
    rw [hB] at h1
    have hmem : (B * V) 0 0 ∈ S :=
      ⟨fun h => hb0 (zero_dvd_iff.1 (h ▸ h1)), B * V, hAB.mul_right hV, rfl⟩
    exact (key _ hmem h1).trans h2

  choose t ht using hcol B hAB hB
  let t' : Fin (n + 1) → R := fun j => if j = 0 then 0 else -t j
  have hL : IsUnit (1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R))) :=
    isUnit_one_add_vecMulVec _ _ (by simp [t'])
  have hAB1 := hAB.mul_left hL
  have e1 := addRow_apply t' 0 B
  generalize (1 + vecMulVec t' (Pi.single (0 : Fin (n + 1)) (1 : R))) * B = B1 at hAB1 e1
  have h1_00 : B1 0 0 = b := by rw [e1]; simp [t', hB]
  have h1_c : ∀ i : Fin n, B1 i.succ 0 = 0 := by
    intro i
    rw [e1, ht, hB]
    simp [t', Fin.succ_ne_zero]
    ring

  choose s hs using hrow B1 hAB1 h1_00
  let s' : Fin (n + 1) → R := fun j => if j = 0 then 0 else -s j
  have hRt : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s') :=
    isUnit_one_add_vecMulVec _ _ (by simp [s'])
  have hAB2 := hAB1.mul_right hRt
  have e2 := addCol_apply s' 0 B1
  generalize B1 * (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) s') = B2 at hAB2 e2
  have h2_00 : B2 0 0 = b := by rw [e2]; simp [s', h1_00]
  have h2_c : ∀ i : Fin n, B2 i.succ 0 = 0 := by
    intro i
    rw [e2, h1_c]
    simp
  have h2_r : ∀ k : Fin n, B2 0 k.succ = 0 := by
    intro k
    rw [e2, hs, h1_00]
    simp [s', Fin.succ_ne_zero]
  refine ⟨b, B2.submatrix Fin.succ Fin.succ, ?_, ?_⟩
  · have h := eq_blk B2 h2_r h2_c
    rw [h2_00] at h
    rw [← h]
    exact hAB2
  · intro i k
    have hU3 : IsUnit (1 + vecMulVec (Pi.single (0 : Fin (n + 1)) (1 : R)) (Pi.single i.succ 1)) :=
      isUnit_one_add_vecMulVec _ _ (by simp [Fin.succ_ne_zero])
    have e3 := addRow_apply (Pi.single (0 : Fin (n + 1)) (1 : R)) i.succ B2
    have h := hrow _ (hAB2.mul_left hU3) (by rw [e3]; simp [h2_00, h2_c]) k.succ
    rw [e3] at h
    simpa [h2_r] using h

theorem smith (n : ℕ) : ∀ A : Matrix (Fin n) (Fin n) R,
    ∃ d : Fin n → R, Eqv A (diagonal d) ∧ ∀ i j, i ≤ j → d i ∣ d j := by
  induction n with
  | zero =>
    intro A
    refine ⟨fun i => i.elim0, ?_, fun i => i.elim0⟩
    have e : A = diagonal (fun i : Fin 0 => i.elim0) := by
      ext i
      exact i.elim0
    rw [← e]
    exact Eqv.refl A
  | succ n ih =>
    intro A
    obtain ⟨b, D, hAD, hbD⟩ := exists_blk A
    obtain ⟨d, hD, hd⟩ := ih D
    obtain ⟨U, V, hU, hV, hUV⟩ := hD
    have hbd : ∀ i, b ∣ d i := by
      intro i
      have h := congrFun (congrFun hUV i) i
      rw [Matrix.diagonal_apply_eq] at h
      rw [← h, Matrix.mul_apply]
      refine Finset.dvd_sum fun l _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.dvd_sum fun m _ => ?_
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hbD m l) _) _
    have eb : blk b (diagonal d) = diagonal (Fin.cons b d : Fin (n + 1) → R) := by
      ext a c
      cases a using Fin.cases with
      | zero =>
        cases c using Fin.cases with
        | zero => simp
        | succ k => simp [Matrix.diagonal_apply, (Fin.succ_ne_zero k).symm]
      | succ i =>
        cases c using Fin.cases with
        | zero => simp [Matrix.diagonal_apply, Fin.succ_ne_zero]
        | succ k => simp [Matrix.diagonal_apply, Fin.succ_inj]
    refine ⟨Fin.cons b d, ?_, ?_⟩
    · rw [← eb]
      exact hAD.trans (Eqv.blk ⟨U, V, hU, hV, hUV⟩ b)
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact dvd_refl _
        | succ j' => simpa using hbd j'
      | succ i' =>
        cases j using Fin.cases with
        | zero => exact absurd hij (by simp [Fin.succ_ne_zero])
        | succ j' => simpa using hd i' j' (Fin.succ_le_succ_iff.mp hij)

end PI.SmithWork
end
